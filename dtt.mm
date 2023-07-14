$( dtt.mm  25-Feb-2016 $)

$(
                      PUBLIC DOMAIN DEDICATION

This file is placed in the public domain per the Creative Commons Public
Domain Dedication. http://creativecommons.org/licenses/publicdomain/

Mario Carneiro - email: di.gama at gmail.com

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c set $.   $( Typecode for variables (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c oterm $. $( Typecode for open terms (syntax) $)
  $c mterm $. $( Typecode for middle terms (syntax) $)
  $c wff $.   $( Typecode for deductions (syntax). $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c := $.    $( Definitional equality $)
  $c |= $.    $( Context separator $)
  $c , $.     $( Separator $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c \ $.     $( Lambda expression $)
  $c T. $.    $( Truth wff $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C D F R S T $.  $( Term variables $)
  $v ph ps ch th $.  $( Wff variables $)
  $v OA OB OC OD OE MA MB $.  $( Special variables $)

  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.

  $( Let variable ` A ` be a term. $)
  tA $f term A $.
  $( Let variable ` B ` be a term. $)
  tB $f term B $.
  $( Let variable ` C ` be a term. $)
  tC $f term C $.
  $( Let variable ` D ` be a term. $)
  tD $f term D $.
  $( Let variable ` F ` be a term. $)
  tF $f term F $.
  $( Let variable ` R ` be a term. $)
  tR $f term R $.
  $( Let variable ` S ` be a term. $)
  tS $f term S $.
  $( Let variable ` T ` be a term. $)
  tT $f term T $.

  $( Let variable ` OA ` be an open term. $)
  oA $f oterm OA $.
  $( Let variable ` OB ` be an open term. $)
  oB $f oterm OB $.
  $( Let variable ` OC ` be an open term. $)
  oC $f oterm OC $.
  $( Let variable ` OD ` be an open term. $)
  oD $f oterm OD $.
  $( Let variable ` OE ` be an open term. $)
  oE $f oterm OE $.

  $( Let variable ` MA ` be a middle term. $)
  mA $f mterm MA $.
  $( Let variable ` MB ` be a middle term. $)
  mB $f mterm MB $.

  $( Let variable ` x ` be a set variable. $)
  vx $f set x $.
  $( Let variable ` y ` be a set variable. $)
  vy $f set y $.
  $( Let variable ` z ` be a set variable. $)
  vz $f set z $.
  $( Let variable ` f ` be a set variable. $)
  vf $f set f $.
  $( Let variable ` g ` be a set variable. $)
  vg $f set g $.
  $( Let variable ` p ` be a set variable. $)
  vp $f set p $.
  $( Let variable ` q ` be a set variable. $)
  vq $f set q $.

  $( A set is a term.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  tv $a term x $.
  $( A term is a middle term.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  mt $a mterm A $.
  $( A middle term is an open term.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  om $a oterm MA $.
  $( An open term with parentheses is a term.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  to $a term ( OA ) $.

  $( A combination (function application).  Middle terms are used for ensuring
     left-associativity of combination, with higher precedence than lambda
     abstraction.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  mc $a mterm MA B $.
  $( A lambda abstraction is a term.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  ol $a oterm \ x : OA , OB $.

  $( Typehood assertion.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wk $a wff OA : OB $.
  $( Definitional equality.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wde $a wff OA := OB $.
  $( Context operator.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wa $a wff ( ph , ps ) $.
  $( A deduction is a wff.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wi $a wff ( ph |= ps ) $.
  $( Tautology is a wff.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  wtru $a wff T. $.

  ${
    idi.1 $e |- ph $.
    $( The identity inference.  (Contributed by Mario Carneiro,
       25-Feb-2016.) $)
    idi $p |- ph $=
      idi.1 $.
  $}

  $( Axiom _Simp_.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-1 $a |- ( ph |= ( ps |= ph ) ) $.

  $( Axiom _Frege_.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-2 $a |- ( ( ph |= ( ps |= ch ) ) |= ( ( ph |= ps ) |= ( ph |= ch ) ) ) $.

  ${
    $( Minor premise for modus ponens. $)
    min $e |- ph $.
    $( Major premise for modus ponens. $)
    maj $e |- ( ph |= ps ) $.
    $( Rule of Modus Ponens.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
    ax-mp $a |- ps $.
  $}

  ${
    a1i.1 $e |- ph $.
    $( Change an empty context into any context.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    a1i $p |- ( ps |= ph ) $=
      wph wps wph wi a1i.1 wph wps ax-1 ax-mp $.
  $}

  ${
    mpd.1 $e |- ( ph |= ps ) $.
    mpd.2 $e |- ( ph |= ( ps |= ch ) ) $.
    $( Modus ponens deduction.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    mpd $p |- ( ph |= ch ) $=
      wph wps wi wph wch wi mpd.1 wph wps wch wi wi wph wps wi wph wch wi wi
      mpd.2 wph wps wch ax-2 ax-mp ax-mp $.
  $}

  ${
    syl.1 $e |- ( ph |= ps ) $.
    syl.2 $e |- ( ps |= ch ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syl $p |- ( ph |= ch ) $=
      wph wps wch syl.1 wps wch wi wph syl.2 a1i mpd $.
  $}

  $( The identity inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  id $p |- ( ph |= ph ) $=
    wph wph wph wi wph wph wph ax-1 wph wph wph wi ax-1 mpd $.

  ${
    ax-imp.1 $e |- ( ph |= ( ps |= ch ) ) $.
    $( Importation for context conjunction.  (Contributed by Mario Carneiro,
       25-Feb-2016.) $)
    ax-imp $a |- ( ( ph , ps ) |= ch ) $.

    $( Importation for context conjunction.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    imp $p |- ( ( ph , ps ) |= ch ) $=
      wph wps wch ax-imp.1 ax-imp $.
  $}

  ${
    ax-ex.1 $e |- ( ( ph , ps ) |= ch ) $.
    $( Exportation for context conjunction.  (Contributed by Mario Carneiro,
       25-Feb-2016.) $)
    ax-ex $a |- ( ph |= ( ps |= ch ) ) $.

    $( Exportation for context conjunction.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    ex $p |- ( ph |= ( ps |= ch ) ) $=
      wph wps wch ax-ex.1 ax-ex $.
  $}

  ${
    jca.1 $e |- ( ph |= ps ) $.
    jca.2 $e |- ( ph |= ch ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    jca $p |- ( ph |= ( ps , ch ) ) $=
      wph wch wps wch wa jca.2 wph wps wch wps wch wa wi jca.1 wps wch wps wch
      wa wps wch wa id ex syl mpd $.
  $}

  ${
    syl2anc.1 $e |- ( ph |= ps ) $.
    syl2anc.2 $e |- ( ph |= ch ) $.
    syl2anc.3 $e |- ( ( ps , ch ) |= th ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syl2anc $p |- ( ph |= th ) $=
      wph wps wch wa wth wph wps wch syl2anc.1 syl2anc.2 jca syl2anc.3 syl $.
  $}

  ${
    mp2an.1 $e |- ph $.
    mp2an.2 $e |- ps $.
    mp2an.3 $e |- ( ( ph , ps ) |= ch ) $.
    $( An inference based on modus ponens.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    mp2an $p |- ch $=
      wph wch mp2an.1 wph wph wps wch wph wph mp2an.1 a1i wps wph mp2an.2 a1i
      mp2an.3 syl2anc ax-mp $.
  $}

  $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  simpl $p |- ( ( ph , ps ) |= ph ) $=
    wph wps wph wph wps ax-1 imp $.

  $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  simpr $p |- ( ( ph , ps ) |= ps ) $=
    wph wps wps wps wps wi wph wps id a1i imp $.

  $( "Definition" of tautology.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  ax-tru $a |- T. $.

  $( Tautology is provable.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tru $p |- T. $=
    ax-tru $.

  ${
    trud.1 $e |- ( T. |= ph ) $.
    $( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    trud $p |- ph $=
      wtru wph tru trud.1 ax-mp $.
  $}

  ${
    mpdan.1 $e |- ( ph |= ps ) $.
    mpdan.2 $e |- ( ( ph , ps ) |= ch ) $.
    $( Modus ponens deduction.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    mpdan $p |- ( ph |= ch ) $=
      wph wps wch mpdan.1 wph wps wch mpdan.2 ex mpd $.
  $}

  ${
    simpld.1 $e |- ( ph |= ( ps , ch ) ) $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    simpld $p |- ( ph |= ps ) $=
      wph wps wch wa wps simpld.1 wps wch simpl syl $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    simprd $p |- ( ph |= ch ) $=
      wph wps wch wa wch simpld.1 wps wch simpr syl $.
  $}

  ${
    ancoms.1 $e |- ( ( ph , ps ) |= ch ) $.
    $( Swap the two elements of a context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    ancoms $p |- ( ( ps , ph ) |= ch ) $=
      wps wph wa wph wps wch wps wph simpr wps wph simpl ancoms.1 syl2anc $.
  $}

  ${
    adantr.1 $e |- ( ph |= ch ) $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    adantr $p |- ( ( ph , ps ) |= ch ) $=
      wph wps wa wph wch wph wps simpl adantr.1 syl $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    adantl $p |- ( ( ps , ph ) |= ch ) $=
      wph wps wch wph wps wch adantr.1 adantr ancoms $.
  $}

  ${
    anim2i.1 $e |- ( ph |= ps ) $.
    $( Introduce a right conjunct.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    anim1i $p |- ( ( ph , ch ) |= ( ps , ch ) ) $=
      wph wch wa wps wch wph wch wps anim2i.1 adantr wph wch simpr jca $.

    $( Introduce a left conjunct.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    anim2i $p |- ( ( ch , ph ) |= ( ch , ps ) ) $=
      wch wph wa wch wps wch wph simpl wph wch wps anim2i.1 adantl jca $.
  $}

  ${
    syldan.1 $e |- ( ( ph , ps ) |= ch ) $.
    syldan.2 $e |- ( ( ph , ch ) |= th ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    syldan $p |- ( ( ph , ps ) |= th ) $=
      wph wps wa wph wch wth wph wps simpl syldan.1 syldan.2 syl2anc $.
  $}

  ${
    sylan.1 $e |- ( ph |= ps ) $.
    sylan.2 $e |- ( ( ps , ch ) |= th ) $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    sylan $p |- ( ( ph , ch ) |= th ) $=
      wph wch wa wps wch wa wth wph wps wch sylan.1 anim1i sylan.2 syl $.
  $}

  ${
    an32s.1 $e |- ( ( ( ph , ps ) , ch ) |= th ) $.
    $( Commutation identity for context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    an32s $p |- ( ( ( ph , ch ) , ps ) |= th ) $=
      wph wch wa wps wa wph wps wa wch wth wph wch wa wph wps wph wch simpl
      anim1i wph wch wa wps wch wph wch simpr adantr an32s.1 syl2anc $.

    $( Associativity for context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    anasss $p |- ( ( ph , ( ps , ch ) ) |= th ) $=
      wps wch wa wph wth wps wph wch wth wps wph wa wph wps wa wch wth wph wps
      wph wps wa wph wps wa id ancoms an32s.1 sylan an32s ancoms $.
  $}

  ${
    anassrs.1 $e |- ( ( ph , ( ps , ch ) ) |= th ) $.
    $( Associativity for context.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    anassrs $p |- ( ( ( ph , ps ) , ch ) |= th ) $=
      wph wps wa wch wa wph wps wch wa wth wph wps wa wch wph wph wps simpl
      adantr wph wps wa wps wch wph wps simpr anim1i anassrs.1 syl2anc $.
  $}

  $( Reflexivity of equality.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  ax-deid $a |- OA := OA $.

  $( Reflexivity of equality.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  deid $p |- OA := OA $=
    oA ax-deid $.

  $( Reflexivity of equality.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  deidd $p |- ( ph |= OA := OA ) $=
    oA oA wde wph oA deid a1i $.

  $( Transitivity of equality.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  ax-detr $a |- ( ( OA := OB , OC := OB ) |= OA := OC ) $.

  ${
    $( Symmetry of equality.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desym $p |- ( OA := OB |= OB := OA ) $=
      oA oB wde oB oB wde oA oB wde oB oA wde oA oB wde oB deidd oA oB wde id
      oB oB oA ax-detr syl2anc $.
  $}

  ${
    desymi.1 $e |- OA := OB $.
    $( Symmetry of equality.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desymi $p |- OB := OA $=
      oA oB wde oB oA wde desymi.1 oA oB desym ax-mp $.

    ${
      desymi.2 $e |- OC := OB $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      detr4i $p |- OA := OC $=
        oA oB wde oC oB wde oA oC wde desymi.1 desymi.2 oA oB oC ax-detr mp2an
        $.
    $}

    detri.2 $e |- OB := OC $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    detri $p |- OA := OC $=
      oA oB oC desymi.1 oB oC detri.2 desymi detr4i $.
  $}

  ${
    desymd.1 $e |- ( ph |= OA := OB ) $.
    $( Symmetry of equality.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    desymd $p |- ( ph |= OB := OA ) $=
      wph oA oB wde oB oA wde desymd.1 oA oB desym syl $.

    ${
      desymd.2 $e |- ( ph |= OC := OB ) $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      detr4d $p |- ( ph |= OA := OC ) $=
        wph oA oB wde oC oB wde oA oC wde desymd.1 desymd.2 oA oB oC ax-detr
        syl2anc $.
    $}

    detrd.2 $e |- ( ph |= OB := OC ) $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    detrd $p |- ( ph |= OA := OC ) $=
      wph oA oB oC desymd.1 wph oB oC detrd.2 desymd detr4d $.
  $}

  ${
    3detr4d.1 $e |- ( ph |= OA := OB ) $.
    ${
      3detr4d.2 $e |- ( ph |= OC := OA ) $.
      3detr4d.3 $e |- ( ph |= OD := OB ) $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      3detr4d $p |- ( ph |= OC := OD ) $=
        wph oC oA oD 3detr4d.2 wph oD oB oA 3detr4d.3 3detr4d.1 detr4d detr4d
        $.
    $}

    ${
      3detr3d.2 $e |- ( ph |= OA := OC ) $.
      3detr3d.3 $e |- ( ph |= OB := OD ) $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      3detr3d $p |- ( ph |= OC := OD ) $=
        wph oC oB oD wph oC oA oB wph oA oC 3detr3d.2 desymd 3detr4d.1 detrd
        3detr3d.3 detrd $.
    $}

    ${
      3detr4g.2 $e |- OC := OA $.
      3detr4g.3 $e |- OD := OB $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      3detr4g $p |- ( ph |= OC := OD ) $=
        wph oA oB oC oD 3detr4d.1 oC oA wde wph 3detr4g.2 a1i oD oB wde wph
        3detr4g.3 a1i 3detr4d $.
    $}

    ${
      3detr3g.2 $e |- OA := OC $.
      3detr3g.3 $e |- OB := OD $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      3detr3g $p |- ( ph |= OC := OD ) $=
        wph oA oB oC oD 3detr4d.1 oA oC wde wph 3detr3g.2 a1i oB oD wde wph
        3detr3g.3 a1i 3detr3d $.
    $}
  $}

  $( Definitional equality applied to a typehood assertion.  (Contributed by
     Mario Carneiro, 25-Feb-2016.) $)
  ax-dek $a |- ( ( OA := OB , OC := OD ) |= ( OA : OC |= OB : OD ) ) $.

  $( Reduction of parentheses.  (Contributed by Mario Carneiro,
     25-Feb-2016.) $)
  df-b $a |- ( OA ) := OA $.

  $( Equality theorem for parentheses.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  bd $p |- ( ph |= ( OA ) := OA ) $=
    oA to mt om oA wde wph oA df-b a1i $.

  ${
    bded.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for parentheses.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    bded $p |- ( ph |= ( OA ) := ( OB ) ) $=
      wph oA oB oA to mt om oB to mt om bded.1 oA df-b oB df-b 3detr4g $.
  $}

  ${
    dektri.1 $e |- OA := OB $.
    dektri.2 $e |- OB : OC $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    dektri $p |- OA : OC $=
      oB oC wk oA oC wk dektri.2 oB oA wde oC oC wde oB oC wk oA oC wk wi oA oB
      dektri.1 desymi oC ax-deid oB oA oC oC ax-dek mp2an ax-mp $.
  $}

  ${
    kdetri.1 $e |- OA : OB $.
    kdetri.2 $e |- OB := OC $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    kdetri $p |- OA : OC $=
      oA oB wk oA oC wk kdetri.1 oA oA wde oB oC wde oA oB wk oA oC wk wi oA
      deid kdetri.2 oA oA oB oC ax-dek mp2an ax-mp $.
  $}

  ${
    dektrd.1 $e |- ( ph |= OA := OB ) $.
    dektrd.2 $e |- ( ph |= OB : OC ) $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    dektrd $p |- ( ph |= OA : OC ) $=
      wph oB oC wk oA oC wk dektrd.2 wph oB oA wde oC oC wde oB oC wk oA oC wk
      wi wph oA oB dektrd.1 desymd wph oC deidd oB oA oC oC ax-dek syl2anc mpd
      $.
  $}

  ${
    kdetrd.1 $e |- ( ph |= OA : OB ) $.
    kdetrd.2 $e |- ( ph |= OB := OC ) $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    kdetrd $p |- ( ph |= OA : OC ) $=
      wph oA oB wk oA oC wk kdetrd.1 wph oA oA wde oB oC wde oA oB wk oA oC wk
      wi wph oA deidd kdetrd.2 oA oA oB oC ax-dek syl2anc mpd $.
  $}

  $( The type of a combination.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-kc $a |- ( ( MA : \ x : A , OB , B : A ) |= MA B : MB B ) $.

  $( Equality theorem for a combination.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-cde $a |- ( ( MA := MB , A := B ) |= MA A := MB B ) $.

  ${
    kcd.1 $e |- ( ph |= MA : \ x : A , OB ) $.
    kcd.2 $e |- ( ph |= B : A ) $.
    $( The type of a combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kcd $p |- ( ph |= MA B : MB B ) $=
      wph mA om tA mt om oB vx ol wk tB mt om tA mt om wk tB mA mc om tB mB mc
      om wk kcd.1 kcd.2 tA tB oB mA mB vx ax-kc syl2anc $.
  $}

  ${
    cde12d.1 $e |- ( ph |= MA := MB ) $.
    ${
      cde12d.2 $e |- ( ph |= A := B ) $.
      $( Equality theorem for combination.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      cde12d $p |- ( ph |= MA A := MB B ) $=
        wph mA om mB om wde tA mt om tB mt om wde tA mA mc om tB mB mc om wde
        cde12d.1 cde12d.2 tA tB mA mB ax-cde syl2anc $.
    $}

    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    cde1d $p |- ( ph |= MA A := MB A ) $=
      wph tA tA mA mB cde12d.1 wph tA mt om deidd cde12d $.
  $}

  ${
    cde2d.1 $e |- ( ph |= A := B ) $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    cde2d $p |- ( ph |= MA A := MA B ) $=
      wph tA tB mA mA wph mA om deidd cde2d.1 cde12d $.
  $}

  $( Equality theorem for a lambda abstraction.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-lde1 $a |- ( OA := OB |= \ x : OA , OC := \ x : OB , OC ) $.

  ${
    lde1d.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for a lambda abstraction.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    lde1d $p |- ( ph |= \ x : OA , OC := \ x : OB , OC ) $=
      wph oA oB wde oA oC vx ol oB oC vx ol wde lde1d.1 oA oB oC vx ax-lde1 syl
      $.
  $}

  ${
    $d x ph $.
    ${
      ax-kl.1 $e |- ( ph |= OA : OD ) $.
      ax-kl.2 $e |- ( ( ph , x : OA ) |= OB : OC ) $.
      $( The type of a lambda abstraction.  (Contributed by Mario Carneiro,
         26-Feb-2016.) $)
      ax-kl $a |- ( ph |= \ x : OA , OB : \ x : OA , OC ) $.
    $}

    ${
      ax-lde.2 $e |- ( ( ph , x : OA ) |= OB := OC ) $.
      $( Equality theorem for a lambda abstraction.  (Contributed by Mario
         Carneiro, 26-Feb-2016.) $)
      ax-lde $a |- ( ph |= \ x : OA , OB := \ x : OA , OC ) $.
    $}

    ${
      lded.1 $e |- ( ph |= OB := OC ) $.
      $( Equality theorem for a lambda abstraction.  (Contributed by Mario
         Carneiro, 26-Feb-2016.) $)
      lded $p |- ( ph |= \ x : OA , OB := \ x : OA , OC ) $=
        wph oA oB oC vx wph vx tv mt om oA wk oB oC wde lded.1 adantr ax-lde $.
    $}
  $}

  $( Axiom of eta reduction.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-eta $a |- ( MB : \ y : OA , OC |= \ x : OA , MB x := MB ) $.

  $( Distribution of combination over substitution.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-distrc $a |- ( \ x : OA , MA B ) A :=
                  ( \ x : OA , MA ) A ( ( \ x : OA , B ) A ) $.

  ${
    $d x y $.  $d y A $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    ax-distrl $a |- ( \ x : OA , \ y : OB , OC ) A :=
                    \ y : ( \ x : OA , OB ) A , ( \ x : OA , OC ) A $.
  $}

  $( ` x ` is bound in ` \ x , A ` , $)
  ax-hbl1 $a |- ( A : OA |=
    ( \ x : OA , \ x : OB , OC ) A := \ x : OB , OC ) $.

  ${
    hbl1.1 $e |- ( ph |= A : OA ) $.
    $( Deduction form of ~ ax-hbl1 .  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    hbl1 $p |- ( ph |= ( \ x : OA , \ x : OB , OC ) A := \ x : OB , OC ) $=
      wph tA mt om oA wk tA oA oB oC vx ol vx ol to mt mc om oB oC vx ol wde
      hbl1.1 tA oA oB oC vx ax-hbl1 syl $.
  $}

  ${
    $d x OB $.
    $( If ` x ` does not appear in ` OB ` , then any substitution to ` OB `
       yields ` OB ` again, i.e. ` \ x OB ` is a constant function. $)
    ax-17 $a |- ( A : OA |= ( \ x : OA , OB ) A := OB ) $.

    a17d.1 $e |- ( ph |= A : OA ) $.
    $( Deduction form of ~ ax-17 .  (Contributed by ?who?, 15-Jun-2023.) $)
    a17d $p |- ( ph |= ( \ x : OA , OB ) A := OB ) $=
      wph tA mt om oA wk tA oA oB vx ol to mt mc om oB wde a17d.1 tA oA oB vx
      ax-17 syl $.
  $}

  ${
    $d x ph $.
    hbxfrf.1 $e |- ( ph |= OC := OB ) $.
    hbxfrf.2 $e |- ( ( ps , ph ) |= ( \ x : OA , OB ) A := OB ) $.
    $( Transfer a hypothesis builder to an equivalent expression.  (Contributed
       by Mario Carneiro, 26-Feb-2016.) $)
    hbxfrf $p |- ( ( ps , ph ) |= ( \ x : OA , OC ) A := OC ) $=
      wps wph wa tA oA oB vx ol to mt mc om oB tA oA oC vx ol to mt mc om oC
      hbxfrf.2 wps wph wa tA oA oC vx ol to mt oA oB vx ol to mt wps wph wa oA
      oC vx ol oA oB vx ol wph wps oA oC vx ol oA oB vx ol wde wph oA oC oB vx
      hbxfrf.1 lded adantl bded cde1d wph wps oC oB wde hbxfrf.1 adantl 3detr4d
      $.
  $}

  ${
    hbxfr.1 $e |- OC := OB $.
    hbxfr.2 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    $( Transfer a hypothesis builder to an equivalent expression.  (Contributed
       by Mario Carneiro, 26-Feb-2016.) $)
    hbxfr $p |- ( ph |= ( \ x : OA , OC ) A := OC ) $=
      wph tA oA oC vx ol to mt mc om oC wde wi wtru wph tA oA oC vx ol to mt mc
      om oC wde wph wtru tA oA oC vx ol to mt mc om oC wde wtru wph tA oA oB oC
      vx oC oB wde wtru hbxfr.1 a1i wph wtru tA oA oB vx ol to mt mc om oB wde
      hbxfr.2 adantr hbxfrf ancoms ex trud $.
  $}

  ${
    hbc.1 $e |- ( ph |= ( \ x : OA , MA ) A := MA ) $.
    hbc.2 $e |- ( ph |= ( \ x : OA , B ) A := B ) $.
    $( Hypothesis builder for combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    hbc $p |- ( ph |= ( \ x : OA , MA B ) A := MA B ) $=
      wph tA oA tB mA mc om vx ol to mt mc om tA oA tB mt om vx ol to mt mc om
      to tA oA mA om vx ol to mt mc mc om tB mA mc om tA oA tB mA mc om vx ol
      to mt mc om tA oA tB mt om vx ol to mt mc om to tA oA mA om vx ol to mt
      mc mc om wde wph tA tB oA mA vx ax-distrc a1i wph tA oA tB mt om vx ol to
      mt mc om to tB tA oA mA om vx ol to mt mc mA hbc.1 wph tA oA tB mt om vx
      ol to mt mc om to mt om tA oA tB mt om vx ol to mt mc om tB mt om wph tA
      oA tB mt om vx ol to mt mc om bd hbc.2 detrd cde12d detrd $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.
    hbl.1 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    hbl.2 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( Hypothesis builder for lambda abstraction.  (Contributed by ?who?,
       15-Jun-2023.) $)
    hbl $p |- ( ph |= ( \ x : OA , \ y : OB , OC ) A := \ y : OB , OC ) $=
      wph tA oA oB oC vy ol vx ol to mt mc om tA oA oB vx ol to mt mc om tA oA
      oC vx ol to mt mc om vy ol oB oC vy ol tA oA oB oC vy ol vx ol to mt mc
      om tA oA oB vx ol to mt mc om tA oA oC vx ol to mt mc om vy ol wde wph tA
      oA oB oC vx vy ax-distrl a1i wph tA oA oB vx ol to mt mc om tA oA oC vx
      ol to mt mc om vy ol oB tA oA oC vx ol to mt mc om vy ol oB oC vy ol wph
      tA oA oB vx ol to mt mc om oB tA oA oC vx ol to mt mc om vy hbl.1 lde1d
      wph oB tA oA oC vx ol to mt mc om oC vy hbl.2 lded detrd detrd $.
  $}

  $( Beta-reduce a term.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-beta $a |- ( x : OA |= ( \ x : OA , OB ) x := OB ) $.

  ${
    $d x ph $.
    ax-cl.1 $e |- ( ph |= A : OA ) $.
    ax-cl.2 $e |- ( ( ph , x := A ) |= OB := OC ) $.
    $( Apply a variable substitution.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    ax-cl $a |- ( ph |= ( \ x : OA , OB ) A := ( \ x : OA , OC ) A ) $.

    clf.3 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( Evaluate a lambda expression.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    clf $p |- ( ph |= ( \ x : OA , OB ) A := OC ) $=
      wph tA oA oB vx ol to mt mc om tA oA oC vx ol to mt mc om oC wph tA oA oB
      oC vx ax-cl.1 ax-cl.2 ax-cl clf.3 detrd $.
  $}

  ${
    $d x A $.  $d x OA $.  $d x OC $.
    cl.1 $e |- ( x := A |= OB := OC ) $.
    $( Evaluate a lambda expression.  (Contributed by ?who?, 15-Jun-2023.) $)
    cl $p |- ( A : OA |= ( \ x : OA , OB ) A := OC ) $=
      tA mt om oA wk tA oA oB oC vx tA mt om oA wk id vx tv mt om tA mt om wde
      tA mt om oA wk oB oC wde cl.1 adantl tA oA oC vx ax-17 clf $.
  $}

  ${
    $d x y ph $.  $d x OA $.
    cbvf.1 $e |- ( ph |= OA : OD ) $.
    cbvf.2 $e |- ( ( ph , x : OA ) |= OB : OE ) $.
    cbvf.3 $e |- ( ( ph , x := y ) |= OB := OC ) $.
    ${
      cbvf.4 $e |- ( x : OA |= ( \ y : OA , OB ) x := OB ) $.
      cbvf.5 $e |- ( y : OA |= ( \ x : OA , OC ) y := OC ) $.
      $( Change bound variables in a lambda abstraction.  (Contributed by Mario
         Carneiro, 26-Feb-2016.) $)
      cbvf $p |- ( ph |= \ x : OA , OB := \ y : OA , OC ) $=
        wph oA oB vx ol to mt om oA vy tv oA oB vx ol to mt mc om vy ol oA oB
        vx ol oA oC vy ol wph oA vy tv oA oB vx ol to mt mc om vy ol oA oB vx
        ol to mt om wph oA oB vx ol to mt om oA oE vx ol wk oA vy tv oA oB vx
        ol to mt mc om vy ol oA oB vx ol to mt om wde wph oA oB vx ol to mt om
        oA oB vx ol oA oE vx ol wph oA oB vx ol bd wph oA oB oE oD vx cbvf.1
        cbvf.2 ax-kl dektrd oA oE oA oB vx ol to mt vy vx ax-eta syl desymd wph
        oA oB vx ol bd wph oA vy tv oA oB vx ol to mt mc om oC vy wph vy tv mt
        om oA wk wa vy tv oA oB oC vx wph vy tv mt om oA wk simpr wph vy tv mt
        om oA wk wa wph vx tv mt om vy tv mt om wde oB oC wde wph vy tv mt om
        oA wk simpl cbvf.3 sylan vy tv mt om oA wk wph vy tv oA oC vx ol to mt
        mc om oC wde cbvf.5 adantl clf ax-lde 3detr3d $.
    $}

    $d x OC $.  $d y OB $.
    $( Change bound variables in a lambda abstraction.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    cbv $p |- ( ph |= \ x : OA , OB := \ y : OA , OC ) $=
      wph oA oB oC oD oE vx vy cbvf.1 cbvf.2 cbvf.3 vx tv oA oB vy ax-17 vy tv
      oA oC vx ax-17 cbvf $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Infix operator
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [ ] $.

  $( Infix operator.  (Contributed by Mario Carneiro, 25-Feb-2016.) $)
  tov $a term [ A F B ] $.

  $( Infix operator.  This is a simple metamath way of cleaning up the syntax
     of all these infix operators to make them a bit more readable than the
     curried representation.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  df-ov $a |- [ A F B ] := F A B $.

  ${
    oveq123d.4 $e |- ( ph |= F := S ) $.
    oveq123d.5 $e |- ( ph |= A := C ) $.
    oveq123d.6 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    oveq123d $p |- ( ph |= [ A F B ] := [ C S T ] ) $=
      wph tB tA tF mt mc mc om tT tC tS mt mc mc om tA tB tF tov mt om tC tT tS
      tov mt om wph tB tT tA tF mt mc tC tS mt mc wph tA tC tF mt tS mt
      oveq123d.4 oveq123d.5 cde12d oveq123d.6 cde12d tA tB tF df-ov tC tT tS
      df-ov 3detr4g $.
  $}

  ${
    oveq1d.4 $e |- ( ph |= A := C ) $.
    $( Equality theorem for binary operation.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    oveq1d $p |- ( ph |= [ A F B ] := [ C F B ] ) $=
      wph tA tB tC tF tF tB wph tF mt om deidd oveq1d.4 wph tB mt om deidd
      oveq123d $.

    oveq12d.5 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    oveq12d $p |- ( ph |= [ A F B ] := [ C F T ] ) $=
      wph tA tB tC tF tF tT wph tF mt om deidd oveq1d.4 oveq12d.5 oveq123d $.
  $}

  ${
    oveq2d.4 $e |- ( ph |= B := T ) $.
    $( Equality theorem for binary operation.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    oveq2d $p |- ( ph |= [ A F B ] := [ A F T ] ) $=
      wph tA tB tA tF tT wph tA mt om deidd oveq2d.4 oveq12d $.
  $}

  ${
    oveqd.4 $e |- ( ph |= F := S ) $.
    $( Equality theorem for binary operation.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    oveqd $p |- ( ph |= [ A F B ] := [ A S B ] ) $=
      wph tA tB tA tF tS tB oveqd.4 wph tA mt om deidd wph tB mt om deidd
      oveq123d $.
  $}

  ${
    hbov.1 $e |- ( ph |= ( \ x : OA , F ) A := F ) $.
    hbov.2 $e |- ( ph |= ( \ x : OA , B ) A := B ) $.
    hbov.3 $e |- ( ph |= ( \ x : OA , C ) A := C ) $.
    $( Hypothesis builder for binary operation.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    hbov $p |- ( ph |= ( \ x : OA , [ B F C ] ) A := [ B F C ] ) $=
      wph tA oA tC tB tF mt mc mc om tB tC tF tov mt om vx tB tC tF df-ov wph
      tA tC oA tB tF mt mc vx wph tA tB oA tF mt vx hbov.1 hbov.2 hbc hbov.3
      hbc hbxfr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y OA $.  $d x y OB $.  $d x y OD $.
    ovl.1 $e |- ( ( x := A , y := B ) |= OC := OD ) $.
    $( Evaluate a lambda expression in a binary operation.  (Contributed by
       Mario Carneiro, 26-Feb-2016.) $)
    ovl $p |- ( ( A : OA , B : OB ) |=
      [ A ( \ x : OA , \ y : OB , OC ) B ] := OD ) $=
      tA mt om oA wk tB mt om oB wk wa tA tB oA oB oC vy ol vx ol to tov mt om
      tB tA oA oB oC vy ol vx ol to mt mc mc om oD tA tB oA oB oC vy ol vx ol
      to tov mt om tB tA oA oB oC vy ol vx ol to mt mc mc om wde tA mt om oA wk
      tB mt om oB wk wa tA tB oA oB oC vy ol vx ol to df-ov a1i tA mt om oA wk
      tB mt om oB wk wa tB tA oA oB oC vy ol vx ol to mt mc mc om tB oB tA oA
      oC vx ol to mt mc om vy ol to mt mc om oD tA mt om oA wk tB mt om oB wk
      wa tB tA oA oB oC vy ol vx ol to mt mc oB tA oA oC vx ol to mt mc om vy
      ol to mt tA mt om oA wk tB mt om oB wk wa tA oA oB oC vy ol vx ol to mt
      mc om oB tA oA oC vx ol to mt mc om vy ol oB tA oA oC vx ol to mt mc om
      vy ol to mt om tA mt om oA wk tB mt om oB wk wa tA oA oB oC vy ol oB tA
      oA oC vx ol to mt mc om vy ol vx tA mt om oA wk tB mt om oB wk simpl tA
      mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om wde wa oB oC tA oA oC
      vx ol to mt mc om vy tA mt om oA wk tB mt om oB wk wa vx tv mt om tA mt
      om wde wa oC vx tv oA oC vx ol to mt mc om tA oA oC vx ol to mt mc om tA
      mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om wde wa vx tv oA oC vx
      ol to mt mc om oC tA mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om
      wde wa vx tv mt om oA wk vx tv oA oC vx ol to mt mc om oC wde tA mt om oA
      wk tB mt om oB wk wa vx tv mt om tA mt om wde wa vx tv mt om tA mt om oA
      tA mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om wde simpr tA mt om
      oA wk tB mt om oB wk wa vx tv mt om tA mt om wde tA mt om oA wk tA mt om
      oA wk tB mt om oB wk simpl adantr dektrd oA oC vx ax-beta syl desymd tA
      mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om wde wa vx tv tA oA oC
      vx ol to mt tA mt om oA wk tB mt om oB wk wa vx tv mt om tA mt om wde
      simpr cde2d detrd lded tA mt om oA wk tB mt om oB wk wa tA oA oB tA oA oC
      vx ol to mt mc om vx vy tA mt om oA wk tB mt om oB wk wa tA oA oB vx tA
      mt om oA wk tB mt om oB wk simpl a17d tA mt om oA wk tB mt om oB wk wa tA
      tA oA oA oC vx ol to mt vx tA mt om oA wk tB mt om oB wk wa tA oA oA oC
      vx ol oA oC vx ol to mt om vx oA oC vx ol df-b tA mt om oA wk tB mt om oB
      wk wa tA oA oA oC vx tA mt om oA wk tB mt om oB wk simpl hbl1 hbxfr tA mt
      om oA wk tB mt om oB wk wa tA oA tA mt om vx tA mt om oA wk tB mt om oB
      wk simpl a17d hbc hbl clf tA mt om oA wk tB mt om oB wk wa oB tA oA oC vx
      ol to mt mc om vy ol bd detr4d cde1d tA mt om oA wk tB mt om oB wk wa tB
      oB tA oA oC vx ol to mt mc om oD vy tA mt om oA wk tB mt om oB wk simpr
      tA mt om oA wk tB mt om oB wk wa vy tv mt om tB mt om wde wa tA oA oC oD
      vx tA mt om oA wk tB mt om oB wk wa vy tv mt om tB mt om wde tA mt om oA
      wk tA mt om oA wk tB mt om oB wk simpl adantr tA mt om oA wk tB mt om oB
      wk wa vy tv mt om tB mt om wde wa vy tv mt om tB mt om wde vx tv mt om tA
      mt om wde oC oD wde tA mt om oA wk tB mt om oB wk wa vy tv mt om tB mt om
      wde simpr vx tv mt om tA mt om wde vy tv mt om tB mt om wde oC oD wde
      ovl.1 ancoms sylan tA mt om oA wk tB mt om oB wk wa vy tv mt om tB mt om
      wde wa tA oA oD vx tA mt om oA wk tB mt om oB wk wa vy tv mt om tB mt om
      wde tA mt om oA wk tA mt om oA wk tB mt om oB wk simpl adantr a17d clf tA
      mt om oA wk tB mt om oB wk wa tB oB oD vy tA mt om oA wk tB mt om oB wk
      simpr a17d clf detrd detrd $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Function type
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -> $.

  $( The function type.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tim $a term ( OA -> OB ) $.

  ${
    $d x OA $.  $d x OB $.
    $( Definition of the function type, which is just a constant function.
       (Contributed by Mario Carneiro, 26-Feb-2016.) $)
    df-im $a |- ( OA -> OB ) := \ x : OA , OB $.

    kim2.1 $e |- ( ph |= OC : ( OA -> OB ) ) $.
    $( The type of a combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kim2 $p |- ( ph |= OC : \ x : OA , OB ) $=
      wph oC oA oB tim mt om oA oB vx ol kim2.1 oA oB tim mt om oA oB vx ol wde
      wph oA oB vx df-im a1i kdetrd $.
  $}

  ${
    $d x ph $.  $d x OA $.  $d x OB $.  $d x OC $.  $d x OD $.
    imde1d.1 $e |- ( ph |= OA := OB ) $.
    $( Equality theorem for a constant function.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    imde1d $p |- ( ph |= ( OA -> OC ) := ( OB -> OC ) ) $=
      wph oA oC vx ol oB oC vx ol oA oC tim mt om oB oC tim mt om wph oA oB oC
      vx imde1d.1 lde1d oA oC vx df-im oB oC vx df-im 3detr4g $.

    imde12d.1 $e |- ( ph |= OC := OD ) $.
    $( Equality theorem for a constant function.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    imde12d $p |- ( ph |= ( OA -> OC ) := ( OB -> OD ) ) $=
      wph oA oC tim mt om oB oC tim mt om oB oD tim mt om wph oA oB oC imde1d.1
      imde1d wph oB oC vx ol oB oD vx ol oB oC tim mt om oB oD tim mt om wph oB
      oC oD vx imde12d.1 lded oB oC vx df-im oB oD vx df-im 3detr4g detrd $.
  $}

  ${
    imde2d.1 $e |- ( ph |= OB := OC ) $.
    $( Equality theorem for a constant function.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    imde2d $p |- ( ph |= ( OA -> OB ) := ( OA -> OC ) ) $=
      wph oA oA oB oC wph oA deidd imde2d.1 imde12d $.
  $}

  ${
    $d x ph $.  $d x OA $.  $d x OC $.
    kim1.1 $e |- ( ph |= OA : OD ) $.
    kim1.2 $e |- ( ( ph , x : OA ) |= OB : OC ) $.
    $( The type of a lambda abstraction.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kim1 $p |- ( ph |= \ x : OA , OB : ( OA -> OC ) ) $=
      wph oA oB vx ol oA oC vx ol oA oC tim mt om wph oA oB oC oD vx kim1.1
      kim1.2 ax-kl oA oC vx ol oA oC tim mt om wde wph oA oC tim mt om oA oC vx
      ol oA oC vx df-im desymi a1i kdetrd $.
  $}

  ${
    $d x OA $.  $d x OB $.  $d x OC $.  $d x ph $.
    $( The type of a constant function.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    imval $p |- ( A : OA |= ( OA -> OB ) A := OB ) $=
      tA mt om oA wk tA oA oB tim mt mc om tA oA oB vx ol to mt mc om oB tA mt
      om oA wk tA oA oB tim mt oA oB vx ol to mt oA oB tim mt om oA oB vx ol to
      mt om wde tA mt om oA wk oA oB tim mt om oA oB vx ol oA oB vx ol to mt om
      oA oB vx df-im oA oB vx ol df-b detr4i a1i cde1d tA oA oB vx ax-17 detrd
      $.

    kim.1 $e |- ( ph |= OA : OD ) $.
    kim.2 $e |- ( ph |= OB : OC ) $.
    $( The type of a constant function.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kim $p |- ( ph |= ( OA -> OB ) : ( OA -> OC ) ) $=
      wph oA oB tim mt om oA oB vx ol oA oC tim mt om oA oB tim mt om oA oB vx
      ol wde wph oA oB vx df-im a1i wph oA oB oC oD vx kim.1 wph vx tv mt om oA
      wk oB oC wk kim.2 adantr kim1 dektrd $.
  $}

  ${
    $d x OA $.  $d x OB $.
    kcim.1 $e |- ( ph |= MA : ( OA -> OB ) ) $.
    kcim.2 $e |- ( ph |= B : OA ) $.
    $( The type of a combination.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kcim $p |- ( ph |= MA B : OB ) $=
      wph tB mA mc om tB oA oB tim mt mc om oB wph oA to tB oB mA oA oB tim mt
      vx wph mA om oA oB tim mt om oA to mt om oB vx ol kcim.1 wph oA oB tim mt
      om oA oB vx ol oA to mt om oB vx ol oA oB tim mt om oA oB vx ol wde wph
      oA oB vx df-im a1i wph oA oA to mt om oB vx wph oA to mt om oA wph oA bd
      desymd lde1d detrd kdetrd wph tB mt om oA oA to mt om kcim.2 wph oA to mt
      om oA wph oA bd desymd kdetrd kcd wph tB mt om oA wk tB oA oB tim mt mc
      om oB wde kcim.2 tB oA oB imval syl kdetrd $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y A $.  $d y OB $.  $d y OC $.
    hbim.1 $e |- ( ph |= ( \ x : OA , OB ) A := OB ) $.
    hbim.2 $e |- ( ph |= ( \ x : OA , OC ) A := OC ) $.
    $( The type of a constant function.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    hbim $p |- ( ph |= ( \ x : OA , ( OB -> OC ) ) A := ( OB -> OC ) ) $=
      wph tA oA oB oC vy ol oB oC tim mt om vx oB oC vy df-im wph tA oA oB oC
      vx vy hbim.1 hbim.2 hbl hbxfr $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Types and universes
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c univ $.  $( Typecode for universes (syntax) $)
  $c u0 $.    $( Lowest universe level $)
  $c suc $.   $( Universe successor $)
  $c max $.   $( Universe join $)
  $c imax $.  $( Universe join (variant) $)
  $c u<_ $.   $( Universe ordering $)
  $c Type $.  $( Type of types $)
  $c Prop $.  $( Type of propositions $)
  $c typeof $. $( Typeof operator $)


  $v i j k $.  $( Universe variables $)

  $( Let variable ` i ` be a universe variable. $)
  ui $f univ i $.
  $( Let variable ` j ` be a universe variable. $)
  uj $f univ j $.
  $( Let variable ` k ` be a universe variable. $)
  uk $f univ k $.

  $( The universe zero.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uu0 $a univ u0 $.

  $( The successor function.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  usuc $a univ suc i $.

  $( The max function.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  umax $a univ max i j $.

  $( The imax function, which is equal to ` u0 ` if ` j = u0 ` , otherwise
     ` imax i j = max i j ` .  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uimax $a univ imax i j $.

  $( Comparison of universe levels is a deduction.  The collection of universe
     levels, modeled by the natural numbers, is a join-semilattice with a
     bottom element and a successor function.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  wule $a wff i u<_ j $.

  $( Ordering of universes is reflexive.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-leid $a |- i u<_ i $.

  $( Ordering of universes is transitive.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-letr $a |- ( ( i u<_ j , j u<_ k ) |= i u<_ k ) $.

  $( Zero is the bottom element of the universe order.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-0le $a |- u0 u<_ i $.

  $( Comparison of universe levels is a deduction.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-lesuc $a |- i u<_ suc i $.

  $( The successor function is monotonic.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-sucle $a |- ( i u<_ j |= suc i u<_ suc j ) $.

  $( The maximum function is greater than the first argument.  (Contributed by
     Mario Carneiro, 26-Feb-2016.) $)
  ax-max1 $a |- i u<_ max i j $.

  $( The maximum function is greater than the second argument.  (Contributed by
     Mario Carneiro, 26-Feb-2016.) $)
  ax-max2 $a |- j u<_ max i j $.

  $( If both arguments are below a bound, so is the maximum.  (Contributed by
     Mario Carneiro, 26-Feb-2016.) $)
  ax-lemax $a |- ( ( i u<_ k , j u<_ k ) |= max i j u<_ k ) $.

  $( The imax function is less than the max function.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-imaxle $a |- imax i j u<_ max i j $.

  $( The imax function with zero right argument is zero.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-imax0 $a |- imax i u0 u<_ u0 $.

  $( The imax function with nonzero right argument is equivalent to the max
     function.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ax-imaxsuc $a |- max i suc j u<_ imax i suc j $.

  $( The imax function of equal arguments equals the common value.  This is
     provable for the natural numbers but must be assumed here since we only
     have the first order theory.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-imaxid $a |- i u<_ imax i i $.

  $( The type " ` Type i ` " is the set of all types at universe level ` i ` .
     The lowest one is ` Prop ` , and each Type is in the next higher one.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tty $a term Type i $.

  $( The type of propositions.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  tpp $a term Prop $.

  $( The type of propositions.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  df-pp $a |- Prop := Type u0 $.

  $( The typeof operator returns the universe level in which a type resides.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  uto $a univ typeof OA $.

  $( Each type is in the next higher type.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  kty $a |- Type i : Type suc i $.

  $( The set of universes is a partial order, so two universe levels that are
     less than each other produce definitionally equal type universes.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tyde $a |- ( ( i u<_ j , j u<_ i ) |= Type i := Type j ) $.

  $( A lambda abstraction representing a pi type is a member of the imax of the
     index type and the type of the target types.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  tyim $a |- ( ( OA : Type i , OB : ( OA -> Type j ) ) |=
               OB : Type imax i j ) $.

  ${
    $d x ph $.  $d x OA $.  $d x j $.
    tyld.1 $e |- ( ph |= OA : Type i ) $.
    tyld.2 $e |- ( ( ph , x : OA ) |= OB : Type j ) $.
    $( A lambda abstraction representing a pi type is a member of the imax of
       the index type and the type of the target types.  (Contributed by Mario
       Carneiro, 26-Feb-2016.) $)
    tyld $p |- ( ph |= \ x : OA , OB : Type imax i j ) $=
      wph oA ui tty mt om wk oA oB vx ol oA uj tty mt om tim mt om wk oA oB vx
      ol ui uj uimax tty mt om wk tyld.1 wph oA oB uj tty mt om ui tty mt om vx
      tyld.1 tyld.2 kim1 oA oA oB vx ol ui uj tyim syl2anc $.
  $}

  ${
    $d x ph $.  $d x OA $.
    tylpp.1 $e |- ( ph |= OA : Type i ) $.
    tylpp.2 $e |- ( ( ph , x : OA ) |= OB : Prop ) $.
    $( The type of a forall statement.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    tylpp $p |- ( ph |= \ x : OA , OB : Prop ) $=
      wph oA oB vx ol ui uu0 uimax tty mt om tpp mt om wph oA oB vx ui uu0
      tylpp.1 wph vx tv mt om oA wk wa oB tpp mt om uu0 tty mt om tylpp.2 tpp
      mt om uu0 tty mt om wde wph vx tv mt om oA wk wa df-pp a1i kdetrd tyld ui
      uu0 uimax tty mt om tpp mt om wde wph ui uu0 uimax tty mt om uu0 tty mt
      om tpp mt om ui uu0 uimax uu0 wule uu0 ui uu0 uimax wule ui uu0 uimax tty
      mt om uu0 tty mt om wde ui ax-imax0 ui uu0 uimax ax-0le ui uu0 uimax uu0
      tyde mp2an df-pp detr4i a1i kdetrd $.
  $}

  $( If ` OB ` contains an element, then it is a type, so it resides in some
     type universe, labeled by the typeof operator.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  ax-to $a |- ( OA : OB |= OB : Type typeof OB ) $.

  $( If ` OA ` is in the universe level ` i ` , then ` i ` is at least as large
     as the universe of ` OA ` .  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-tole $a |- ( OA : Type i |= typeof OA u<_ i ) $.

  $( Proof irrelevance for propositions.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  ax-irrel $a |- ( OA : Prop |= ( ( OB : OA , OC : OA ) |= OB := OC ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Zero, one, two
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $c zero zero.rec $.
  $c one one.* one.rec $.
  $c bool tt ff cond $.

  $( The zero type, a type with no elements.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  t0 $a term zero $.

  $( The zero recursor.  (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t0r $a term zero.rec $.

  $( The universe of the zero type.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  k0 $a |- zero : Type suc u0 $.

  $( Definition of the zero recursor, a function to any type.  (Contributed by
     Mario Carneiro, 14-Mar-2016.) $)
  k0r $a |- zero.rec i : \ x : Type i , ( zero -> x ) $.

  $( The type of the zero recursor.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  0val $p |- ( A : Type i |= zero.rec i A : ( zero -> A ) ) $=
    ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
    wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
    ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.

  $( The one type, a type with one element.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  t1 $a term one $.

  $( The sole element of the one type.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  t1s $a term one.* $.

  $( The one recursor.  (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  t1r $a term one.rec $.

  $( Definition of the one type, as the set of all functions from zero to
     itself.  (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  df-1 $a |- one := ( zero -> zero ) $.

  $( Definition of the unique element of the one type, the identity function on
     zero.  (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  df-1s $a |- one.* := \ x : zero , x $.

  $( Definition of the one recursor.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  df-1r $a |- one.rec i := \ x : Type i , \ y : x , \ z : one , y $.

  $( The star is a member of its type.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  k1s $p |- one.* : one $=
    ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
    wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
    ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.

  $( Type of the one recursor.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  k1r $p |- one.rec i : \ x : Type i , ( x -> ( one -> x ) ) $=
    ? $.

  ${
    de1s.1 $e |- ( ph |= OA : Type i ) $.
    de1s.2 $e |- ( ph |= A : OA ) $.
    $( The equality rule for the star.  (Contributed by Mario Carneiro,
       14-Mar-2016.) $)
    de1s $p |- ( ph |= one.rec i A one.* := A ) $=
      ( ol uu0 uimax tty mt om tpp tv wde df-pp a1i kdetrd wule ax-imax0 ax-0le
      wk wa tyld tyde mp2an detr4i ) ABCDHEIJZKLMZNLMZABCDEIFADOLMBUCUDZCUKIKLM
      ZGUKUMPULQRSUEUJUKPAUJUMUKUIITIUITUJUMPEUAUIUBUIIUFUGQUHRS $.
  $}

  $( The boolean type, a type with two elements.  (Contributed by Mario
     Carneiro, 14-Mar-2016.) $)
  t2 $a term bool $.

  $( The first element of the boolean type, "true".  (Contributed by Mario
     Carneiro, 14-Mar-2016.) $)
  ttt $a term tt $.

  $( The second element of the boolean type, "false".  (Contributed by Mario
     Carneiro, 14-Mar-2016.) $)
  tff $a term ff $.

  $( The universe of the zero type.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  k2 $a |- bool : Type suc u0 $.

  $( True is a boolean value.  (Contributed by Mario Carneiro, 14-Mar-2016.) $)
  ktt $a |- tt : bool $.

  $( False is a boolean value.  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  kff $a |- ff : bool $.

  $( The conditional (bool recursor).  (Contributed by Mario Carneiro,
     14-Mar-2016.) $)
  kcd1 $a |- cond i : \ x : Type i , ( bool -> ( x -> ( x -> x ) ) ) $.

  ${
    dett.1 $e |- ( ph |= OA : Type i ) $.
    dett.2 $e |- ( ph |= A : OA ) $.
    dett.3 $e |- ( ph |= B : OA ) $.
    $( The equality rule for the conditional, true case.  (Contributed by Mario
       Carneiro, 14-Mar-2016.) $)
    dett $a |- ( ph |= cond i tt A B := A ) $.

    $( The equality rule for the conditional, false case.  (Contributed by
       Mario Carneiro, 14-Mar-2016.) $)
    deff $a |- ( ph |= cond i ff A B := B ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Sigma type
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c sigma $.
  $c sigma1 $.
  $c sigma2 $.
  $c pair $.
  $c 1st $.
  $c 2nd $.

  $( The sigma type, the equivalent of an indexed disjoint union in ZFC.
     (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  tsig $a term sigma i j $.

  $( The first component function for a sigma type.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  t1st $a term 1st i j $.

  $( The second component function for a sigma type.  (Contributed by Mario
     Carneiro, 26-Feb-2016.) $)
  t2nd $a term 2nd i j $.

  $( The pair function for a sigma type.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  tpair $a term pair i j $.

  $( Type of the sigma type.  (Contributed by Mario Carneiro, 26-Feb-2016.) $)
  ksig $a |- sigma i j : \ x : Type i , \ y : ( x -> Type j ) ,
            ( Type max suc u0 max i j ) $.

  $( Type of the first component function.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  k1st $a |- 1st i j : \ x : Type i , \ y : ( x -> Type j ) ,
              ( sigma i j x y -> x ) $.

  $( Type of the second component function.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  k2nd $a |- 2nd i j : \ x : Type i , \ y : ( x -> Type j ) ,
              \ p : sigma i j x y , y ( sigma1 i j x y p ) $.

  $( Type of the pair function.  (Contributed by Mario Carneiro,
     26-Feb-2016.) $)
  kpair $a |- pair i j : \ x : Type i , \ y : ( x -> Type j ) ,
              \ p : x , ( y p -> sigma i j x y ) $.

  ${
    kpair1.1 $e |- ( ph |= A : Type i ) $.
    kpair1.2 $e |- ( ph |= B : ( A -> Type j ) ) $.
    kpair1.3 $e |- ( ph |= C : A ) $.
    kpair1.4 $e |- ( ph |= D : B C ) $.
    $( Type of the pair function.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    kpaird $p |- ( ph |= pair i j A B C D : sigma i j A B ) $=
      ? $.

    $( Equality theorem for the sigma type.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    desig1 $a |- ( ph |= sigma1 i j A B pair i j A B C D := C ) $.

    $( Equality theorem for the sigma type.  (Contributed by Mario Carneiro,
       26-Feb-2016.) $)
    desig2 $a |- ( ph |= sigma2 i j A B pair i j A B C D := D ) $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Inductive definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  Todo:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/******* Web page format settings *******/

/* Page title, home page link */
htmltitle "Higher-Order Logic Explorer";
htmlhome '<A HREF="mmhol.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="hol.gif" BORDER=0 ALT=' +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check correctness of
   the references. */
htmlbibliography "mmhol.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<FONT COLOR="#0000FF">type</FONT> '
    + '<FONT COLOR="#FF0000">var</FONT> '
    + '<FONT COLOR="#CC33CC">term</FONT>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../holgif/";
althtmldir "../holuni/";


/******* Symbol definitions *******/

htmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  althtmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  latexdef "wff" as "\mathrm{wff}";
htmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  althtmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  latexdef "var" as "\mathrm{var}";
htmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  althtmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  latexdef "type" as "\mathrm{type}";
htmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  althtmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  latexdef "term" as "\mathrm{term}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT='|-' ALIGN=TOP> ";
  althtmldef "|-" as
    '<FONT COLOR="#808080" FACE=sans-serif>&#8866; </FONT>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
  latexdef "|-" as "\vdash";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=':' ALIGN=TOP>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "." as " ";
  althtmldef "." as ' ';
  latexdef "." as "\,";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT='|=' ALIGN=TOP> ";
  althtmldef "|=" as "&#8871;"; latexdef "|=" as "\models";
htmldef "bool" as
    "<IMG SRC='hexstar.gif' WIDTH=11 HEIGHT=19 ALT='*' ALIGN=TOP>";
  althtmldef "bool" as '&lowast;';
  latexdef "bool" as "\ast";
htmldef "ind" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT='iota' ALIGN=TOP>";
  althtmldef "ind" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "ind" as "\iota";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT='-&gt;' ALIGN=TOP> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' ALIGN=TOP>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' ALIGN=TOP>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=',' ALIGN=TOP> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "\" as "<IMG SRC='lambda.gif' WIDTH=9 HEIGHT=19 ALT='\' ALIGN=TOP>";
  althtmldef "\" as '<I>&lambda;</I>';
  latexdef "\" as "\lambda";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT='=' ALIGN=TOP> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "T." as "<IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' ALIGN=TOP>";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' ALIGN=TOP>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' ALIGN=TOP>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "al" as
    "<IMG SRC='_alpha.gif' WIDTH=12 HEIGHT=19 ALT='al' ALIGN=TOP>";
  althtmldef "al" as '<FONT COLOR="#0000FF"><I>&alpha;</I></FONT>';
  latexdef "al" as "\alpha";
htmldef "be" as
    "<IMG SRC='_beta.gif' WIDTH=11 HEIGHT=19 ALT='be' ALIGN=TOP>";
  althtmldef "be" as '<FONT COLOR="#0000FF"><I>&beta;</I></FONT>';
  latexdef "be" as "\beta";
htmldef "ga" as
    "<IMG SRC='_gamma.gif' WIDTH=11 HEIGHT=19 ALT='ga' ALIGN=TOP>";
  althtmldef "ga" as '<FONT COLOR="#0000FF"><I>&gamma;</I></FONT>';
  latexdef "ga" as "\gamma";
htmldef "de" as
    "<IMG SRC='_delta.gif' WIDTH=9 HEIGHT=19 ALT='de' ALIGN=TOP>";
  althtmldef "de" as '<FONT COLOR="#0000FF"><I>&delta;</I></FONT>';
  latexdef "de" as "\delta";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT='x' ALIGN=TOP>";
  althtmldef "x" as '<I><FONT COLOR="#FF0000">x</FONT></I>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT='y' ALIGN=TOP>";
  althtmldef "y" as '<I><FONT COLOR="#FF0000">y</FONT></I>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT='z' ALIGN=TOP>";
  althtmldef "z" as '<I><FONT COLOR="#FF0000">z</FONT></I>';
  latexdef "z" as "z";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT='f' ALIGN=TOP>";
  althtmldef "f" as '<I><FONT COLOR="#FF0000">f</FONT></I>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT='g' ALIGN=TOP>";
  althtmldef "g" as '<I><FONT COLOR="#FF0000">g</FONT></I>';
  latexdef "g" as "g";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT='p' ALIGN=TOP>";
  althtmldef "p" as '<I><FONT COLOR="#FF0000">p</FONT></I>';
  latexdef "p" as "p";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT='q' ALIGN=TOP>";
  althtmldef "q" as '<I><FONT COLOR="#FF0000">q</FONT></I>';
  latexdef "q" as "q";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT='A' ALIGN=TOP>";
  althtmldef "A" as '<I><FONT COLOR="#CC33CC">A</FONT></I>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT='B' ALIGN=TOP>";
  althtmldef "B" as '<I><FONT COLOR="#CC33CC">B</FONT></I>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT='C' ALIGN=TOP>";
  althtmldef "C" as '<I><FONT COLOR="#CC33CC">C</FONT></I>';
  latexdef "C" as "C";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT='F' ALIGN=TOP>";
  althtmldef "F" as '<I><FONT COLOR="#CC33CC">F</FONT></I>';
  latexdef "F" as "F";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT='R' ALIGN=TOP>";
  althtmldef "R" as '<I><FONT COLOR="#CC33CC">R</FONT></I>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT='S' ALIGN=TOP>";
  althtmldef "S" as '<I><FONT COLOR="#CC33CC">S</FONT></I>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT='T' ALIGN=TOP>";
  althtmldef "T" as '<I><FONT COLOR="#CC33CC">T</FONT></I>';
  latexdef "T" as "T";
htmldef "F." as "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='F.' ALIGN=TOP>";
  althtmldef "F." as '&perp;';
  latexdef "F." as "\bot";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT='/\' ALIGN=TOP> ";
  althtmldef "/\" as ' <FONT FACE=sans-serif>&and;</FONT> ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
  latexdef "/\" as "\wedge";
htmldef "~" as "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT='~' ALIGN=TOP> "; 
  althtmldef "~" as '&not; ';
  latexdef "~" as "\lnot";
htmldef "==>" as
    " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='==&gt;' ALIGN=TOP> ";
  althtmldef "==>" as ' &rArr; ';
  latexdef "==>" as "\Rightarrow";
htmldef "!" as "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT='A.' ALIGN=TOP>";
  althtmldef "!" as '<FONT FACE=sans-serif>&forall;</FONT>'; /* &#8704; */
  latexdef "!" as "\forall";
htmldef "?" as "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT='E.' ALIGN=TOP>";
  althtmldef "?" as '<FONT FACE=sans-serif>&exist;</FONT>'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
  latexdef "?" as "\exists";
htmldef "\/" as " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT='\/' ALIGN=TOP> ";
  althtmldef "\/" as ' <FONT FACE=sans-serif> &or;</FONT> ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
  latexdef "\/" as "\vee";
htmldef "?!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT='E!' ALIGN=TOP>";
  althtmldef "?!" as '<FONT FACE=sans-serif>&exist;!</FONT>';
  latexdef "?!" as "\exists{!}";
htmldef "typedef" as "typedef ";
  althtmldef "typedef" as 'typedef ';
  latexdef "typedef" as "\text{ typedef }";
htmldef "1-1" as "1-1 ";
  althtmldef "1-1" as '1-1 ';
  latexdef "1-1" as "\mathrm{1-1}";
htmldef "onto" as "onto ";
  althtmldef "onto" as 'onto ';
  latexdef "onto" as "\mathrm{onto}";
htmldef "@" as
    "<IMG SRC='varepsilon.gif' WIDTH=8 HEIGHT=19 ALT='@' ALIGN=TOP>";
  althtmldef "@" as '&epsilon;';
  latexdef "@" as "\varepsilon";

/* End of typesetting definition section */
$)

$( 456789012345 (79-character line to adjust text window width) 567890123456 $)
