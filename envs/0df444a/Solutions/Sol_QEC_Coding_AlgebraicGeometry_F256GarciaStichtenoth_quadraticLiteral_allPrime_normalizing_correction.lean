-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_allPrime_normalizing_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:19:03.819027+00:00
-- url     : https://prove2.me/submissions/b3fba4fb-f824-4794-b659-4fc4f8a82a0e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_simplePole_baseChange_correction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_artinSchreier_root_order_of_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_integralClosurePlace_order_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem order_neg_one_ne_zero
    {K : Type*} [_root_.Field K] [Algebra F256 K]
    (P : GlobalPlace F256 K) {z : K} (hz : P.order z = -1) : z ≠ 0 := by
  intro hzero
  subst z
  simp [GlobalPlace.order] at hz
private theorem quadraticLiteral_regular_ramificationIdx_eq_one
    {K L : Type*} [_root_.Field K] [_root_.Field L]
    [Algebra F256 K] [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (ha : 0 ≤ P.order a) (y : L)
    (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal = 1 := by
  let O := P.valuationRing
  let C := integralClosure O L
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : Algebra (FractionRing O) (FractionRing C) := FractionRing.liftAlgebra _ _
  letI : Algebra.IsSeparable (FractionRing O) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv O K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    apply IsFractionRing.ringHom_ext (A := O)
    intro t
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv O K).symm (FractionRing.algEquiv C L).symm
      (algebraMap O K t)
  have hd := quadraticLiteral_different_eq_top P a ha y hy hdegree hgen
  have hnot : ¬ H.asIdeal ∣ differentIdeal O C := by
    rw [hd, Ideal.dvd_iff_le]
    intro h
    exact H.isPrime.ne_top (top_unique h)
  letI : Algebra.IsUnramifiedAt O H.asIdeal :=
    (not_dvd_differentIdeal_iff (A := O) (B := C)).mp hnot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal O)
    H.asIdeal (IsDiscreteValuationRing.not_a_field O)]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := O) (p := H.asIdeal)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    {K L : Type*} [_root_.Field K] [_root_.Field L]
    [Algebra F256 K] [Algebra F256 L] [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K) [Finite P.residueField]
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a)
    (b : K) (hb : P.order b = -1 ∨ 0 ≤ P.order b) :
    ∃ c : L,
      (c = 0 ∨ (integralClosurePlace (k := F256) H).order c = -1) ∧
      ((integralClosurePlace (k := F256) H).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (integralClosurePlace (k := F256) H).order (algebraMap K L b + c ^ 2 + c)) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let Q := integralClosurePlace (k := F256) H
  let e := (IsLocalRing.maximalIdeal O).ramificationIdx' H.asIdeal
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have horder (v : K) (hv : v ≠ 0) :
      Q.order (algebraMap K L v) = (e : ℤ) * P.order v :=
    integralClosurePlace_order_algebraMap P H v hv
  rcases hb with hbpole | hbregular
  · have hb0 : b ≠ 0 := order_neg_one_ne_zero P hbpole
    rcases ha with hapole | haregular
    · have ha0 : a ≠ 0 := order_neg_one_ne_zero P hapole
      have hepos : 0 < e := Nat.pos_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver H.asIdeal
          (IsDiscreteValuationRing.not_a_field O))
      have hele : e ≤ 2 :=
        (Ideal.ramificationIdx_le_finrank C K L H.asIdeal).trans_eq hdegree
      obtain ⟨he, hyorder⟩ := P.artinSchreier_root_order_of_simplePole
        Q a y e hepos hele hy (horder a ha0) hapole
      obtain ⟨c, hc, hcorrected⟩ := exists_simplePole_baseChange_correction
        P Q a b y hapole hbpole hyorder hy (fun v hv => by
          rw [horder v hv, he]
          norm_num)
      exact ⟨c, Or.inr hc, hcorrected⟩
    · have he : e = 1 := quadraticLiteral_regular_ramificationIdx_eq_one
        P H a haregular y hy hdegree hgen
      refine ⟨0, Or.inl rfl, Or.inl ?_⟩
      change Q.order (algebraMap K L b + 0 ^ 2 + 0) = -1
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
      rw [horder b hb0, he, hbpole]
      norm_num
  · refine ⟨0, Or.inl rfl, Or.inr ?_⟩
    change 0 ≤ Q.order (algebraMap K L b + 0 ^ 2 + 0)
    simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
    by_cases hb0 : b = 0
    · simp [hb0, Q, GlobalPlace.order]
    · rw [horder b hb0]
      exact mul_nonneg (Nat.cast_nonneg e) hbregular
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
