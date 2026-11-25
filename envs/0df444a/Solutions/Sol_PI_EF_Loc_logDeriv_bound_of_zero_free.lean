-- Prove2me | solution 1 for PI.EF.Loc.logDeriv_bound_of_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:06.383388+00:00
-- url     : https://prove2.me/submissions/326ce89a-080e-44f8-8fe7-a8926111c0dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
namespace PI.EF.Loc
theorem _root_.solution (hDL : PI.DiscLog) {g : ℂ → ℂ} {s₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball s₀ R))
    (hz : ∀ z ∈ ball s₀ R, g z ≠ 0) (hb : ∀ z ∈ ball s₀ R, ‖g z‖ ≤ Real.exp M * ‖g s₀‖) :
    ∀ z ∈ closedBall s₀ r, ‖deriv g z / g z‖ ≤ 4 * (r + R) / (R - r) ^ 2 * M := by
  intro z hzr
  obtain ⟨L, hL0, hLd, hLe⟩ := hDL g s₀ R hg hz
  have hR : 0 < R := hr.trans hrR
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hg0 : 0 < ‖g s₀‖ := norm_pos_iff.mpr (hz s₀ hs₀)
  have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun x hx =>
    (hLd x hx).differentiableAt.differentiableWithinAt
  have hre : ∀ x ∈ ball s₀ R, (L x).re ≤ M := by
    intro x hx
    have h1 := hb x hx
    rw [hLe x hx, norm_mul, Complex.norm_exp, mul_comm (Real.exp M)] at h1
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_left h1 hg0)
  have hmem : ∀ u ∈ ball (0 : ℂ) R, s₀ + u ∈ ball s₀ R := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    simpa [dist_eq_norm] using hu
  have hFd : DifferentiableOn ℂ (fun u => L (s₀ + u)) (ball 0 R) := by
    intro u hu
    have h1 : DifferentiableAt ℂ L (s₀ + u) := (hLd _ (hmem u hu)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun v : ℂ => s₀ + v) u := differentiableAt_id.const_add s₀
    exact (h1.comp u h2).differentiableWithinAt
  have hFre : MapsTo (fun u => L (s₀ + u)) (ball 0 R) {w | w.re ≤ M} :=
    fun u hu => hre _ (hmem u hu)
  have hF0 : (fun u => L (s₀ + u)) 0 = 0 := by simp [hL0]
  have hρR : (r + R) / 2 < R := by linarith
  have hbound : ∀ x ∈ closedBall s₀ ((r + R) / 2),
      ‖L x‖ ≤ 2 * M * ((r + R) / 2) / (R - (r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hu : x - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := Complex.borelCaratheodory_zero hM hFd hFre hR hu hF0
    have e : s₀ + (x - s₀) = x := by ring
    simp only [e] at h1
    refine h1.trans ?_
    have hpos : 0 < R - (r + R) / 2 := by linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    nlinarith [mul_nonneg (mul_nonneg hM.le hR.le) (sub_nonneg.mpr hx)]
  have hδ : 0 < (R - r) / 2 := by linarith
  have hzr' : ‖z - s₀‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hzr; exact hzr
  have hsub : closedBall z ((R - r) / 2) ⊆ closedBall s₀ ((r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have : ‖x - s₀‖ ≤ ‖x - z‖ + ‖z - s₀‖ := by
      have := norm_add_le (x - z) (z - s₀)
      simpa using this
    linarith
  have hsubB : closedBall s₀ ((r + R) / 2) ⊆ ball s₀ R := closedBall_subset_ball hρR
  have hdc : DiffContOnCl ℂ L (ball z ((R - r) / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hδ.ne']
    exact hLdiff.mono (hsub.trans hsubB)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc
    (fun x hx => hbound x (hsub (sphere_subset_closedBall hx)))
  have hzB : z ∈ ball s₀ R := hsubB (hsub (mem_closedBall_self hδ.le))
  rw [(hLd z hzB).deriv] at hc
  refine hc.trans (le_of_eq ?_)
  have e1 : R - (r + R) / 2 = (R - r) / 2 := by ring
  have hne : R - r ≠ 0 := by linarith
  rw [e1]
  field_simp
  ring
end PI.EF.Loc
