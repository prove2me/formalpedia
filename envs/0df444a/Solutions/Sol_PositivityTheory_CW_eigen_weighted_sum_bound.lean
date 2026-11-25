-- Prove2me | solution 1 for PositivityTheory.CW.eigen_weighted_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:54.412437+00:00
-- url     : https://prove2.me/submissions/60f9771b-b8ea-4a92-95ea-8711beb98965

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_KFiniteInclusion
import Theorems.Thm_PositivityTheory_CW_WeightedEigenSum_pow_eig
import Theorems.Thm_PositivityTheory_CW_WeightedEigenSum_wsum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A0 → FunctionalCalculusLaws → B5 := by
  intro _ _ n ε V _ _ E _ ι b μ hb f s K hK hS hs v
  have hv : v = ∑ i ∈ (b.repr v).support, b.repr v i • b i := by
    conv_lhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hpos : ∀ i, 0 < (1 + μ i) ^ s := fun i => pow_pos (by linarith [hb.nonneg i]) s
  have heig : ∀ i, ((1 + casimirK ε E) ^ s) (b i) = (((1 + μ i) ^ s : ℝ) : ℂ) • b i :=
    fun i => WeightedEigenSum.pow_eig _ (μ i) (b i) (hb.eig i) s
  have hw : ((1 + casimirK ε E) ^ s) v =
      ∑ i ∈ (b.repr v).support, (b.repr v i * (((1 + μ i) ^ s : ℝ) : ℂ)) • b i := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig, smul_smul]
  have hfv : f v = inner ℂ (∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i) (((1 + casimirK ε E) ^ s) v) := by
    rw [hw, hb.on.inner_sum]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    have h1 : ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ) * (((1 + μ i) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    linear_combination (-(b.repr v i * f (b i))) * h1
  have hu2 : ‖∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 ≤ K ^ 2 := by
    have e : ‖∑ i ∈ (b.repr v).support,
        (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 =
        ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, hb.on.inner_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_conj, mul_pow]
    have e2 : ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 ≤
        ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h0 : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      have h1 : ((1 + μ i) ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hb.nonneg i]))
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖f (b i)‖) h0) (sub_nonneg.mpr h1)]
    have e3 : ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 ≤ K ^ 2 :=
      WeightedEigenSum.wsum_le μ hb.nonneg hb.fin (fun i => ‖f (b i)‖ ^ 2) (fun i => sq_nonneg _) s hs K hS _
    linarith
  have hu := (pow_le_pow_iff_left₀ (norm_nonneg _) hK two_ne_zero).mp hu2
  rw [hfv]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
end PositivityTheory.CW
