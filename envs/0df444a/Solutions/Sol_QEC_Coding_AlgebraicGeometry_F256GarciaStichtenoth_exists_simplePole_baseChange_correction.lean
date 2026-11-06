-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePole_baseChange_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:07:44.344981+00:00
-- url     : https://prove2.me/submissions/e0c5a68f-6e9e-4c3a-b3b4-bbd3162684d9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticNormalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_unit_square_add_maximalIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_order_regular_mul_simplePole_add_regular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
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
private theorem valuation_eq_one_of_order_eq_zero
    {K : Type*} [_root_.Field K] [Algebra F256 K]
    (P : GlobalPlace F256 K) {z : K} (hz : z ≠ 0)
    (horder : P.order z = 0) : P.valuation z = 1 := by
  have hvaluation_ne : P.valuation z ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hz
  have hlog : WithZero.log (P.valuation z) = 0 := by
    unfold GlobalPlace.order at horder
    omega
  calc
    P.valuation z = WithZero.exp (WithZero.log (P.valuation z)) :=
      (WithZero.exp_log hvaluation_ne).symm
    _ = 1 := by rw [hlog]; simp
private theorem order_pos_of_mem_maximalIdeal
    {K : Type*} [_root_.Field K] [Algebra F256 K]
    (P : GlobalPlace F256 K) (w : P.valuationRing)
    (hw : w ∈ IsLocalRing.maximalIdeal P.valuationRing)
    (hw0 : (w : K) ≠ 0) :
    0 < P.order (w : K) := by
  have hvaluation_lt : P.valuation (w : K) < 1 := by
    rw [Valuation.mem_maximalIdeal_iff] at hw
    exact hw
  have hvaluation_ne : P.valuation (w : K) ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hw0
  have hlog_lt : WithZero.log (P.valuation (w : K)) < WithZero.log 1 :=
    (WithZero.log_lt_log hvaluation_ne one_ne_zero).mpr hvaluation_lt
  rw [WithZero.log_one] at hlog_lt
  unfold GlobalPlace.order
  omega
private theorem artinSchreier_correction_identity
    {L : Type*} [_root_.Field L] [CharP L 2]
    (x z y u w : L)
    (hx : x ^ 2 + x = z)
    (hy : y = z * (u ^ 2 + w)) :
    y + (u * x) ^ 2 + u * x = (u - u ^ 2) * x + z * w := by
  have htwo : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [hy, ← hx]
  linear_combination ((x ^ 2 + x) * u ^ 2) * htwo
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
    [Algebra F256 K] [Algebra K L] [Algebra F256 L]
    (P : GlobalPlace F256 K) [Finite P.residueField]
    (Q : GlobalPlace F256 L)
    (z y : K) (x : L)
    (hz : P.order z = -1) (hy : P.order y = -1)
    (hx : Q.order x = -1)
    (hequation : x ^ 2 + x = algebraMap K L z)
    (horder_algebraMap : ∀ v : K, v ≠ 0 →
      Q.order (algebraMap K L v) = 2 * P.order v) :
    ∃ c : L,
      Q.order c = -1 ∧
        (Q.order (algebraMap K L y + c ^ 2 + c) = -1 ∨
          0 ≤ Q.order (algebraMap K L y + c ^ 2 + c)) := by
  have hz_ne : z ≠ 0 := order_neg_one_ne_zero P hz
  have hy_ne : y ≠ 0 := order_neg_one_ne_zero P hy
  have hratio_ne : y / z ≠ 0 := div_ne_zero hy_ne hz_ne
  have hratio_order : P.order (y / z) = 0 := by
    rw [div_eq_mul_inv, P.order_mul hy_ne (inv_ne_zero hz_ne),
      P.order_inv, hz, hy]
    norm_num
  have hratio_regular : GlobalPlace.RegularAt P (y / z) :=
    (P.regularAt_iff_order_nonnegative hratio_ne).mpr (by omega)
  let ratio : P.valuationRing :=
    ⟨y / z, (P.mem_valuationRing_iff (y / z)).mpr hratio_regular⟩
  have hratio_not_maximal :
      ratio ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change ¬P.valuation (y / z) < 1
    rw [valuation_eq_one_of_order_eq_zero P hratio_ne hratio_order]
    exact lt_irrefl 1
  obtain ⟨u, w, hratio_ring, hu, hw⟩ :=
    exists_unit_square_add_maximalIdeal P ratio hratio_not_maximal
  have hratio : y / z = (u : K) ^ 2 + (w : K) := by
    have hratio_field :=
      congrArg (fun v : P.valuationRing => (v : K)) hratio_ring
    simp only [ratio, map_add, map_pow] at hratio_field ⊢
    exact hratio_field
  let transformed : L :=
    (algebraMap K L (u : K) - algebraMap K L (u : K) ^ 2) * x +
      algebraMap K L (z * (w : K))
  have hlift_regular (v : K) (hv : GlobalPlace.RegularAt P v) :
      GlobalPlace.RegularAt Q (algebraMap K L v) := by
    by_cases hv0 : v = 0
    · subst v
      simp [GlobalPlace.RegularAt]
    · have hmap_ne : algebraMap K L v ≠ 0 :=
        by simpa only [map_zero] using (algebraMap K L).injective.ne hv0
      apply (Q.regularAt_iff_order_nonnegative hmap_ne).mpr
      rw [horder_algebraMap v hv0]
      have horder : 0 ≤ P.order v :=
        (P.regularAt_iff_order_nonnegative hv0).mp hv
      omega
  have hu_regular :
      GlobalPlace.RegularAt Q (algebraMap K L (u : K)) :=
    hlift_regular (u : K) u.property
  have hu_mem : algebraMap K L (u : K) ∈ Q.valuationRing :=
    (Q.regularAt_iff_mem_valuationRing _).mp hu_regular
  have hu_sq_mem : algebraMap K L (u : K) ^ 2 ∈ Q.valuationRing := by
    rw [pow_two]
    exact Q.valuationRing.mul_mem _ _ hu_mem hu_mem
  have hcoefficient_regular :
      GlobalPlace.RegularAt Q
        (algebraMap K L (u : K) - algebraMap K L (u : K) ^ 2) :=
    (Q.regularAt_iff_mem_valuationRing _).mpr
      (Q.valuationRing.sub_mem hu_mem hu_sq_mem)
  have herror_lower_regular : GlobalPlace.RegularAt P (z * (w : K)) := by
    by_cases hw0 : (w : K) = 0
    · rw [hw0, mul_zero]
      simp [GlobalPlace.RegularAt]
    · have hproduct0 : z * (w : K) ≠ 0 := mul_ne_zero hz_ne hw0
      apply (P.regularAt_iff_order_nonnegative hproduct0).mpr
      rw [P.order_mul hz_ne hw0, hz]
      have hw_order : 0 < P.order (w : K) :=
        order_pos_of_mem_maximalIdeal P w hw hw0
      omega
  have herror_regular :
      GlobalPlace.RegularAt Q (algebraMap K L (z * (w : K))) :=
    hlift_regular (z * (w : K)) herror_lower_regular
  have hactual :
      Q.order transformed = -1 ∨ 0 ≤ Q.order transformed := by
    exact order_regular_mul_simplePole_add_regular Q x
      (algebraMap K L (u : K) - algebraMap K L (u : K) ^ 2)
      (algebraMap K L (z * (w : K))) hx hcoefficient_regular herror_regular
  let c : L := algebraMap K L (u : K) * x
  have hu_ne : (u : K) ≠ 0 := by
    intro hu0
    apply hu
    have hu_eq : u = 0 := Subtype.ext hu0
    rw [hu_eq]
    exact (IsLocalRing.maximalIdeal P.valuationRing).zero_mem
  have hu_valuation : P.valuation (u : K) = 1 := by
    apply le_antisymm u.property
    apply le_of_not_gt
    intro hlt
    apply hu
    rw [Valuation.mem_maximalIdeal_iff]
    exact hlt
  have hu_order : P.order (u : K) = 0 := by
    unfold GlobalPlace.order
    rw [hu_valuation, WithZero.log_one]
    norm_num
  have hmap_u_ne : algebraMap K L (u : K) ≠ 0 :=
    by simpa only [map_zero] using (algebraMap K L).injective.ne hu_ne
  have hx_ne : x ≠ 0 := order_neg_one_ne_zero Q hx
  have hc : Q.order c = -1 := by
    dsimp only [c]
    rw [Q.order_mul hmap_u_ne hx_ne,
      horder_algebraMap (u : K) hu_ne, hu_order, hx]
    norm_num
  refine ⟨c, hc, ?_⟩
  have hy_eq : y = z * ((u : K) ^ 2 + (w : K)) := by
    have h := (div_eq_iff hz_ne).mp hratio
    simpa only [mul_comm] using h
  have hembedded_y :
      algebraMap K L y =
        algebraMap K L z *
          (algebraMap K L (u : K) ^ 2 + algebraMap K L (w : K)) := by
    rw [hy_eq, map_mul, map_add, map_pow]
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap F256 K).injective 2
  letI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  have htranslated :
      algebraMap K L y + c ^ 2 + c = transformed := by
    simpa only [c, transformed, map_mul] using
      artinSchreier_correction_identity x (algebraMap K L z)
        (algebraMap K L y) (algebraMap K L (u : K))
          (algebraMap K L (w : K)) hequation hembedded_y
  rw [htranslated]
  exact hactual
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
