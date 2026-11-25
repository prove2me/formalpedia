-- Prove2me | solution 1 for PositivityTheory.RL.Delta.exists_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:26:18.916512+00:00
-- url     : https://prove2.me/submissions/65db70c8-fda1-4055-9545-91b9edaa4e79

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff
namespace PositivityTheory.RL.Delta
theorem _root_.solution : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t := by
  set E : ℂ → ℂ := fun z => cexp (2 * π * I * z) with hE
  have hEd : Differentiable ℂ E := by rw [hE]; fun_prop
  have hd : Differentiable ℂ (dslope E 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hEd.differentiableOn
  have hc : ContDiff ℝ ∞ (fun t : ℝ => dslope E 0 (t : ℂ)) :=
    (hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hmul : ∀ t : ℝ, (t : ℂ) * dslope E 0 t = cexp (2 * π * I * t) - 1 := by
    intro t
    have := sub_smul_dslope E 0 (t : ℂ)
    simpa [hE] using this
  have hne : ∀ t ∈ Metric.ball (0 : ℝ) 1, dslope E 0 (t : ℂ) ≠ 0 := by
    intro t ht h0
    by_cases h : t = 0
    · subst h
      have hD : HasDerivAt E (cexp (2 * π * I * 0) * (2 * π * I * 1)) 0 :=
        ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp
      rw [Complex.ofReal_zero, dslope_same, hD.deriv] at h0
      simp [Real.pi_ne_zero] at h0
    · have h1 := hmul t
      rw [h0, mul_zero, eq_comm, sub_eq_zero, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2 : (t : ℂ) = k := by
        have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ h3
        rw [hk]; ring
      have h4 : t = k := by exact_mod_cast h2
      rw [mem_ball_zero_iff, Real.norm_eq_abs, h4] at ht
      have h5 : |k| < 1 := by exact_mod_cast ht
      have h6 : k = 0 := Int.abs_lt_one_iff.1 h5
      exact h (by rw [h4, h6]; simp)
  refine ⟨fun t => (dslope E 0 (t : ℂ))⁻¹, hc.contDiffOn.inv hne, fun t ht => ?_⟩
  rw [← hmul t, mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one]
end PositivityTheory.RL.Delta
