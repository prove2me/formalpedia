-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.JCC.Ck.partials_continuous_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:09.816085+00:00
-- url     : https://prove2.me/submissions/a460adec-90a7-4183-9053-fa5b23d0069e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CkDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_PCkPartials
import Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_d
import Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_succ
import Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_psum_seg_norm
import Theorems.Thm_PI_UnitaryGroupMassFormula_JCC_Ck_abs_le_of_mem_uIcc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.JCC PI.UnitaryGroupMassFormula.JCC.Ck
namespace PI.UnitaryGroupMassFormula.JCC.Ck
theorem _root_.solution : PartialsContinuousDifferentiable := by
  intro d E _ _ V F D hV hD hF y hy
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set c' : ℝ := c / (d + 1) with hc'
  have hc'pos : 0 < c' := by positivity
  have hev : ∀ᶠ z in 𝓝 y, z ∈ V ∧ ∀ i, ‖D i z - D i y‖ ≤ c' := by
    refine (hV.eventually_mem hy).and (Filter.eventually_all.mpr (fun i => ?_))
    have hcont : ContinuousAt (D i) y := (hD i).continuousAt (hV.mem_nhds hy)
    filter_upwards [hcont (Metric.closedBall_mem_nhds (D i y) hc'pos)] with z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hh
  have hstep : ∀ i : Fin d, ‖F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y‖
      ≤ c' * ‖h‖ := by
    intro i
    set p := psum y h i.val with hp
    have hmem : ∀ t ∈ Set.uIcc 0 (h i), p + t • Pi.single i (1 : ℝ) ∈ Metric.ball y δ := by
      intro t ht
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (psum_seg_norm y h i (abs_le_of_mem_uIcc ht)) hh
    have hderiv : ∀ t ∈ Set.uIcc 0 (h i),
        HasDerivWithinAt (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ)) - s • D i y)
          (D i (p + t • Pi.single i (1 : ℝ)) - D i y) (Set.uIcc 0 (h i)) t := by
      intro t ht
      have h0 := hF _ (hball _ (hmem t ht)).1 i
      have h0' : HasDerivAt (fun u : ℝ => F (p + t • Pi.single i (1 : ℝ) + u • Pi.single i (1 : ℝ)))
          (D i (p + t • Pi.single i (1 : ℝ))) (t - t) := by
        rw [sub_self]
        exact h0
      have h4 := HasDerivAt.comp_sub_const t t h0'
      have hfun : (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ))) =
          fun s => F (p + t • Pi.single i (1 : ℝ) + (s - t) • Pi.single i (1 : ℝ)) := by
        funext s
        congr 1
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have h3 : HasDerivAt (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ)))
          (D i (p + t • Pi.single i (1 : ℝ))) t := by
        rw [hfun]
        exact h4
      have h2 : HasDerivAt (fun s : ℝ => s • D i y) (D i y) t := by
        simpa using (hasDerivAt_id t).smul_const (D i y)
      exact (h3.sub h2).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.uIcc 0 (h i), ‖D i (p + t • Pi.single i (1 : ℝ)) - D i y‖ ≤ c' :=
      fun t ht => (hball _ (hmem t ht)).2 i
    have hmvt := (convex_uIcc (0 : ℝ) (h i)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    have hg : (F (p + h i • Pi.single i (1 : ℝ)) - h i • D i y) - (F (p + (0 : ℝ) • Pi.single i (1 : ℝ)) - (0 : ℝ) • D i y)
        = F (p + h i • Pi.single i (1 : ℝ)) - F p - h i • D i y := by
      rw [zero_smul, zero_smul, add_zero, sub_zero]
      abel
    rw [hg, sub_zero] at hmvt
    calc _ ≤ c' * ‖h i‖ := hmvt
      _ ≤ c' * ‖h‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) hc'pos.le
  have htel : ∑ i : Fin d, (F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y)
      = F (y + h) - F y - (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) h := by
    rw [Finset.sum_sub_distrib]
    have hs : ∀ i : Fin d, F (psum y h i.val + h i • Pi.single i (1 : ℝ)) = F (psum y h (i.val + 1)) :=
      fun i => by rw [psum_succ]
    simp only [hs]
    have hr := Fin.sum_univ_eq_sum_range (fun k => F (psum y h (k + 1)) - F (psum y h k)) d
    rw [hr, Finset.sum_range_sub (fun k => F (psum y h k)) d, psum_d, psum_zero, ContinuousLinearMap.sum_apply]
    first
    | rfl
    | simp
  rw [← htel]
  calc ‖∑ i : Fin d, (F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y)‖
      ≤ ∑ i : Fin d, c' * ‖h‖ := norm_sum_le_of_le _ (fun i _ => hstep i)
    _ = d * c' * ‖h‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ c * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
        rw [hc', ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
end PI.UnitaryGroupMassFormula.JCC.Ck
