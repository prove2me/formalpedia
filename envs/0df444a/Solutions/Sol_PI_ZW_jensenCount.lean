-- Prove2me | solution 1 for PI.ZW.jensenCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:28:22.661171+00:00
-- url     : https://prove2.me/submissions/ad1525d9-0929-425e-bcec-587dde5059a7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
import Theorems.Thm_PI_ZW_order_ne_top_of_ball
import Theorems.Thm_PI_ZW_divisor_eq_order

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution : JensenCount := by
  intro f c M hf hfc hM1 hbd S hS
  have hR : |(19 / 10 : ℝ)| = 19 / 10 := abs_of_pos (by norm_num)
  have hf' : AnalyticOnNhd ℂ f (closedBall c |(19 / 10 : ℝ)|) := by rw [hR]; exact hf
  have hDnn : 0 ≤ MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'
  have hfin : (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).finiteSupport (isCompact_closedBall _ _)
  have hSD : ∀ u ∈ S, MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u =
      (analyticOrderNatAt f u : ℤ) ∧ 1 ≤ analyticOrderNatAt f u ∧ 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ 37 / 20 := by
    intro u hu
    obtain ⟨hub, hfu⟩ := hS hu
    have hub' : u ∈ closedBall c (19 / 10) := closedBall_subset_closedBall (by norm_num) hub
    have hdiv := divisor_eq_order hf hfc le_rfl hub'
    have hne := order_ne_top_of_ball hf hfc hub'
    refine ⟨by rw [hR]; exact hdiv, ?_, ?_, ?_⟩
    · by_contra h0
      push_neg at h0
      have h00 : analyticOrderNatAt f u = 0 := by omega
      have hord : analyticOrderAt f u = 0 := by rw [← Nat.cast_analyticOrderNatAt hne, h00]; rfl
      rcases analyticOrderAt_eq_zero.1 hord with h | h
      · exact h (hf u hub')
      · exact h hfu
    · have : u ≠ c := by rintro rfl; exact hfc hfu
      exact norm_pos_iff.2 (sub_ne_zero.2 this.symm)
    · rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hub
  have hSsub : S ⊆ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support := by
    intro u hu
    obtain ⟨h1, h2, -, -⟩ := hSD u hu
    simp only [Function.mem_support, h1]
    exact_mod_cast (by omega : analyticOrderNatAt f u ≠ 0)
  have hSfin : S.Finite := hfin.subset hSsub
  refine ⟨hSfin, ?_⟩
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := c) (R := 19 / 10) (by norm_num) hf' hfc
  have hup : Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) ≤ Real.log M := by
    apply Real.circleAverage_mono_on_of_le_circle
    · exact MeromorphicOn.circleIntegrable_log_norm (hf'.mono sphere_subset_closedBall).meromorphicOn
    · intro x hx
      rw [hR] at hx
      by_cases h0 : f x = 0
      · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM1
      · exact Real.log_le_log (norm_pos_iff.2 h0) (hbd x hx)
  set g : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) *
    Real.log (19 / 10 * ‖c - u‖⁻¹) with hg
  have hgnn : ∀ u, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support
    · have hdu : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) := by
        exact_mod_cast hDnn u
      have hin := (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).supportWithinDomain hu
      rw [hR] at hin
      have hcu : ‖c - u‖ ≤ 19 / 10 := by rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hin
      apply mul_nonneg hdu
      rcases (norm_nonneg (c - u)).eq_or_lt with h0 | h0
      · rw [← h0, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ h0]; linarith
    · simp only [Function.mem_support, not_not] at hu
      simp [hg, hu]
  have hgsupp : Function.support g ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    simp [hg, h0]
  have hfs : ∑ᶠ u, g u = ∑ u ∈ hfin.toFinset, g u := finsum_eq_sum_of_support_subset g hgsupp
  have hsub2 : hSfin.toFinset ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hSsub hu
  have hlow : ∑ u ∈ hSfin.toFinset, g u ≤ ∑ u ∈ hfin.toFinset, g u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun u _ _ => hgnn u
  have hLpos : 0 < Real.log ((19 / 10) / (37 / 20)) := Real.log_pos (by norm_num)
  have hterm : ∀ u ∈ hSfin.toFinset, (analyticOrderNatAt f u : ℝ) * Real.log ((19 / 10) / (37 / 20)) ≤ g u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hSD u hu
    simp only [hg, h1]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) h3 h4
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hM0 : 0 < M := by linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, le_div_iff₀ hLpos, Finset.sum_mul,
    Real.log_div hM0.ne' hfc0.ne']
  have hsum := Finset.sum_le_sum hterm
  have hJ' : ∑ᶠ u, g u = Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) - Real.log ‖f c‖ := by
    rw [hJ]; simp only [hg]; ring
  linarith
end PI.ZW
