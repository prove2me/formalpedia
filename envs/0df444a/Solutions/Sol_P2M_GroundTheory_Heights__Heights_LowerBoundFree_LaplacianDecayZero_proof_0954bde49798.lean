-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_proof_0954bde49798
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:27.165288+00:00
-- url     : https://prove2.me/submissions/b0ceb86f-f38a-4fe1-b59e-62bd64eeacdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PLaplacianDecayZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian MeasureTheory Filter Topology
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
namespace LaplacianDecayZero
theorem _root_.solution : LaplacianDecayZero.Statement := by
  intro v C R₀ hv hdec
  have hD2c : Continuous (iteratedFDeriv ℝ 2 v) := hv.continuous_iteratedFDeriv le_rfl
  have hdiff : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun y : ℂ => ‖y‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hc : Tendsto (fun y : ℂ => C / ‖y‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hn)
    refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hc
    filter_upwards [hn.eventually_gt_atTop R₀] with y hy
    exact (hdec y hy).1

  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Metric.closedBall (0 : ℂ) (max R₀ 1),
      ‖iteratedFDeriv ℝ 2 v y‖ ≤ M :=
    (isCompact_closedBall 0 (max R₀ 1)).exists_bound_of_continuousOn hD2c.continuousOn
  have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
  have hMR : 0 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)
  have hbound : ∀ y : ℂ, ‖iteratedFDeriv ℝ 2 v y‖ ≤
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    by_cases hy : ‖y‖ ≤ max R₀ 1
    · have h1 := hM y (by simpa using hy)
      have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + max R₀ 1) ^ 3 := by gcongr
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
            mul_le_mul (h1.trans (le_abs_self M)) h2 (by positivity) (abs_nonneg M)
        _ ≤ _ := by linarith [abs_nonneg C]
    · push Not at hy
      have hR0 : R₀ < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
      have hy1 : 1 < ‖y‖ := lt_of_le_of_lt hR1 hy
      have h1 := (hdec y hR0).2
      have h3 : ‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3 ≤ |C| := by
        rw [le_div_iff₀ (by positivity)] at h1
        exact h1.trans (le_abs_self C)
      have h4 : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
        calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8 * ‖y‖ ^ 3 := by ring
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3
          ≤ ‖iteratedFDeriv ℝ 2 v y‖ * (8 * ‖y‖ ^ 3) := by gcongr
        _ = 8 * (‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3) := by ring
        _ ≤ 8 * |C| := by gcongr
        _ ≤ _ := by linarith
  have hK : Integrable (fun y : ℂ =>
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _

  have hpart : ∀ e : ℂ, ‖e‖ = 1 → Integrable (fun y => iteratedFDeriv ℝ 2 v y ![e, e]) := by
    intro e he
    refine hK.mono' ((continuous_eval_const (![e, e] : Fin 2 → ℂ)).comp hD2c).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖iteratedFDeriv ℝ 2 v y ![e, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 v y‖ * ∏ i, ‖(![e, e] : Fin 2 → ℂ) i‖ :=
          (iteratedFDeriv ℝ 2 v y).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 v y‖ := by simp [Fin.prod_univ_two, he]
      _ ≤ _ := hbound y
  have hform : ∀ y e : ℂ, iteratedFDeriv ℝ 2 v y ![e, e] = fderiv ℝ (fderiv ℝ v) y e e := by
    intro y e
    rw [iteratedFDeriv_two_apply]
    rfl
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding

  have htr : ∀ e : ℂ, ‖e‖ = 1 →
      (∫ y, iteratedFDeriv ℝ 2 v y ![e, e]) =
        ∫ p : ℝ × ℝ, iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e] ∧
      Integrable (fun p : ℝ × ℝ =>
        iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e])
        (volume.prod volume) := by
    intro e he
    exact ⟨(hmp.integral_comp hemb _).symm, (hmp.integrable_comp_emb hemb).mpr (hpart e he)⟩
  have hz1 : ∫ y, iteratedFDeriv ℝ 2 v y ![1, 1] = 0 := by
    obtain ⟨h1, h2⟩ := htr 1 (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod_symm _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun b => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim ((b : ℂ) * Complex.I) 1 (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext x
    rw [hform, show Complex.measurableEquivRealProd.symm (x, b) = (b : ℂ) * Complex.I + (x : ℂ) * 1 from
      Complex.ext (by simp) (by simp)]
  have hzI : ∫ y, iteratedFDeriv ℝ 2 v y ![Complex.I, Complex.I] = 0 := by
    obtain ⟨h1, h2⟩ := htr Complex.I (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim (a : ℂ) Complex.I (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext t
    rw [hform, show Complex.measurableEquivRealProd.symm (a, t) = (a : ℂ) + (t : ℂ) * Complex.I from
      Complex.ext (by simp) (by simp)]
  have hΔ := laplacian_eq_iteratedFDeriv_complexPlane v
  have h1 := hpart 1 (by simp)
  have hI := hpart Complex.I (by simp)
  refine ⟨?_, ?_⟩
  · rw [hΔ]
    exact h1.add hI
  · rw [hΔ, integral_add h1 hI, hz1, hzI, add_zero]
end LaplacianDecayZero
end GroundTheory.Heights₂.Heights.LowerBoundFree
