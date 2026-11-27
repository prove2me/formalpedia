-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma.periodic_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:20.367081+00:00
-- url     : https://prove2.me/submissions/d226abc9-09b4-4525-86c6-24b310fd70eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodicSchwarzLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma
open Complex Filter Function Function.Periodic Metric Set
open scoped Topology Real
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma
theorem _root_.solution {g : ℂ → ℂ} {M T t B : ℝ} (hM : 0 < M) (ht : 0 < t) (htT : t < T)
    (hper : Periodic g M) (hdiff : ∀ z : ℂ, -T < z.im → DifferentiableAt ℂ g z)
    (hzero : Tendsto g (comap im atTop) (𝓝 0)) (hB : ∀ z : ℂ, z.im = -t → ‖g z‖ ≤ B) :
    ‖g 0‖ ≤ Real.exp (-2 * π * t / M) * B := by
  have hM0 : (M : ℝ) ≠ 0 := hM.ne'
  have hT : 0 < T := ht.trans htT
  set F := cuspFunction M g with hF
  set R := Real.exp (2 * π * t / M) with hRdef
  have hR : 0 < R := Real.exp_pos _
  have h1R : 1 < R := by
    have := Real.exp_lt_exp.2 (show (0 : ℝ) < 2 * π * t / M by positivity)
    rw [Real.exp_zero] at this
    rw [hRdef]
    exact this
  have hF0 : F 0 = 0 := cuspFunction_zero_of_zero_at_inf hM hzero
  have hdiffF : DifferentiableOn ℂ F (closedBall 0 R) := by
    intro q hq
    apply DifferentiableAt.differentiableWithinAt
    by_cases hq0 : q = 0
    · subst hq0
      have hev : ∀ᶠ z : ℂ in comap im atTop, 0 ≤ z.im :=
        tendsto_comap.eventually (eventually_ge_atTop 0)
      exact differentiableAt_cuspFunction_zero hM hper
        (hev.mono fun z hz => hdiff z (by linarith)) (hzero.isBigO_one ℝ)
    · rw [← qParam_right_inv hM0 hq0]
      apply differentiableAt_cuspFunction hM0 hper
      apply hdiff
      have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
      have hqR : ‖q‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hq
      have hlog : Real.log ‖q‖ ≤ 2 * π * t / M := by
        calc Real.log ‖q‖ ≤ Real.log R := Real.log_le_log hqn hqR
          _ = 2 * π * t / M := by rw [hRdef, Real.log_exp]
      have key : M / (2 * π) * Real.log ‖q‖ ≤ t := by
        calc M / (2 * π) * Real.log ‖q‖ ≤ M / (2 * π) * (2 * π * t / M) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = t := by field_simp
      rw [im_invQParam]
      have : -M / (2 * π) * Real.log ‖q‖ = -(M / (2 * π) * Real.log ‖q‖) := by ring
      rw [this]
      linarith
  have hdsl : DifferentiableOn ℂ (dslope F 0) (closedBall 0 R) :=
    (differentiableOn_dslope (closedBall_mem_nhds 0 hR)).2 hdiffF
  have hdc : DiffContOnCl ℂ (dslope F 0) (ball 0 R) :=
    hdsl.diffContOnCl_ball subset_rfl
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖dslope F 0 z‖ ≤ B / R := by
    intro z hz
    rw [frontier_ball 0 hR.ne', mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact hR.ne' hz.symm
    rw [dslope_of_ne _ hz0, slope_def_field, hF0, sub_zero, sub_zero, norm_div, hz]
    apply div_le_div_of_nonneg_right _ hR.le
    rw [hF, cuspFunction_eq_of_nonzero _ _ hz0]
    apply hB
    rw [im_invQParam, hz, hRdef, Real.log_exp]
    field_simp
  have h1 : (1 : ℂ) ∈ closure (ball (0 : ℂ) R) :=
    subset_closure (by simpa [mem_ball, dist_zero_right] using h1R)
  have hmain := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront h1
  have hq1 : qParam M 0 = 1 := by simp [qParam]
  have hg0 : g 0 = dslope F 0 1 := by
    rw [dslope_of_ne _ one_ne_zero, slope_def_field, hF0, sub_zero, sub_zero, div_one,
      ← hq1, hF, eq_cuspFunction hM0 hper]
  rw [hg0]
  calc ‖dslope F 0 1‖ ≤ B / R := hmain
    _ = Real.exp (-2 * π * t / M) * B := by
      rw [hRdef, show -2 * π * t / M = -(2 * π * t / M) by ring, Real.exp_neg, div_eq_mul_inv,
        mul_comm]
end ReciprocityTheory.ChartRestriction.G.FD.PeriodicSchwarzLemma
