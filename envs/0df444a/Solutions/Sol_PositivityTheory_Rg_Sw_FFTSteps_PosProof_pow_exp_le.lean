-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.PosProof.pow_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:58.778363+00:00
-- url     : https://prove2.me/submissions/76798c5b-ac03-4f92-aef5-07a92fd87498

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
theorem _root_.solution (n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    t ^ n * Real.exp (-(t ^ 2)) ≤ C * (1 + t) ^ (-(3 : ℝ)) := by
  refine ⟨((n + 3).factorial : ℝ) * Real.exp 2, fun t ht => ?_⟩
  have h1 : 0 < 1 + t := by linarith
  have hr : (1 + t) ^ (-(3 : ℝ)) = ((1 + t) ^ 3)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hA : t ^ n ≤ (1 + t) ^ n := pow_le_pow_left₀ ht (by linarith) n
  have hB : (1 + t) ^ (n + 3) ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) := by
    have h := Real.pow_div_factorial_le_exp (1 + t) h1.le (n + 3)
    rwa [div_le_iff₀ (by positivity), mul_comm] at h
  have hC : Real.exp (1 + t) * Real.exp (-(t ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 1 / 2)])
  calc t ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3
      ≤ (1 + t) ^ n * Real.exp (-(t ^ 2)) * (1 + t) ^ 3 := by gcongr
    _ = (1 + t) ^ (n + 3) * Real.exp (-(t ^ 2)) := by ring
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp (1 + t) * Real.exp (-(t ^ 2)) := by gcongr
    _ ≤ ((n + 3).factorial : ℝ) * Real.exp 2 := by
      rw [mul_assoc]
      gcongr
end PositivityTheory.Rg.Sw.FFTSteps.PosProof
