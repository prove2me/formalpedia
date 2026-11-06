-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.ramificationIdx_eq_one_of_unit_different
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:59:54.0108+00:00
-- url     : https://prove2.me/submissions/bda7f968-fcc5-4410-812d-b891208d1e45

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
section
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]
omit [Algebra F256 K] in
private theorem integralClosure_ramificationIdx_eq_one_of_different_eq_top
    {O : Type*} [CommRing O] [Algebra O K] [IsFractionRing O K]
    [Algebra O L] [IsScalarTower O K L]
    [IsDedekindDomain O] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    [Module.IsTorsionFree O (integralClosure O L)]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    [H.asIdeal.LiesOver p]
    (hd : differentIdeal O (integralClosure O L) = ⊤) :
    p.ramificationIdx' H.asIdeal = 1 := by
  let C := integralClosure O L
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : Algebra (FractionRing O) (FractionRing C) := FractionRing.liftAlgebra _ _
  letI : Algebra.IsSeparable (FractionRing O) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv O K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    apply IsFractionRing.ringHom_ext (A := O)
    intro x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv O K).symm (FractionRing.algEquiv C L).symm
      (algebraMap O K x)
  have hnot : ¬ H.asIdeal ∣ differentIdeal O C := by
    rw [hd, Ideal.dvd_iff_le]
    intro h
    exact H.isPrime.ne_top (top_unique h)
  letI : Algebra.IsUnramifiedAt O H.asIdeal :=
    (not_dvd_differentIdeal_iff (A := O) (B := C)).mp hnot
  have hp0 : p ≠ ⊥ := by
    rw [Ideal.over_def H.asIdeal p]
    exact Ideal.under_ne_bot O H.ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p H.asIdeal hp0]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := O) (p := H.asIdeal)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]
omit [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {O : Type*} [CommRing O] [Algebra O K] [IsFractionRing O K]
    [Algebra O L] [IsScalarTower O K L]
    [IsDedekindDomain O] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    [Module.IsTorsionFree O (integralClosure O L)]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    [H.asIdeal.LiesOver p]
    (hd : differentIdeal O (integralClosure O L) = ⊤) :
    p.ramificationIdx' H.asIdeal = 1 :=
  integralClosure_ramificationIdx_eq_one_of_different_eq_top (K := K) p H hd
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
