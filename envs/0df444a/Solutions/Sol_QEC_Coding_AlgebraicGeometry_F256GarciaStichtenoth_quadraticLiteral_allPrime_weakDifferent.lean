-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:54.578756+00:00
-- url     : https://prove2.me/submissions/74a1afd3-60f1-48ae-9313-9b48edac7831

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_map_maximalIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_of_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_integralClosurePlace_order_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


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
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    [Algebra F256 L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    multiplicity H.asIdeal
        (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
      2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal - 1) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  rcases ha with hpole | hregular
  · have ha0 : a ≠ 0 := by
      intro h
      simp [h, GlobalPlace.order] at hpole
    have he0 : 0 < m.ramificationIdx' H.asIdeal :=
      Nat.pos_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver H.asIdeal hm0)
    have he2 : m.ramificationIdx' H.asIdeal ≤ 2 := by
      calc
        m.ramificationIdx' H.asIdeal ≤ Module.finrank K L :=
          Ideal.ramificationIdx_le_finrank C K L H.asIdeal
        _ = 2 := hdegree
    have he := (P.artinSchreier_root_order_of_simplePole
      (integralClosurePlace (k := F256) H) a y
      (m.ramificationIdx' H.asIdeal) he0 he2 hy
      (integralClosurePlace_order_algebraMap P H a ha0) hpole).1
    have hd := quadraticLiteral_different_eq_map_maximalIdeal P a hpole y hy hdegree
    rw [hd]
    have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hm0
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0 H.isPrime]
    change m.ramificationIdx' H.asIdeal = 2 * (m.ramificationIdx' H.asIdeal - 1)
    rw [he]
  · have hd := quadraticLiteral_different_eq_top P a hregular y hy hdegree hgen
    have he := integralClosure_ramificationIdx_eq_one_of_different_eq_top
      (K := K) (L := L) m H hd
    have hmult : multiplicity H.asIdeal (differentIdeal O C) = 0 := by
      rw [hd]
      apply multiplicity_eq_zero.mpr
      rw [Ideal.dvd_iff_le]
      intro h
      exact H.isPrime.ne_top (top_unique h)
    change multiplicity H.asIdeal (differentIdeal O C) =
      2 * (m.ramificationIdx' H.asIdeal - 1)
    rw [hmult, he]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
