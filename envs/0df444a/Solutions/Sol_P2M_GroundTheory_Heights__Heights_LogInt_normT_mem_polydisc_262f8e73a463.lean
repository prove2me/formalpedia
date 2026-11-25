-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_normT_mem_polydisc_262f8e73a463
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:29.659506+00:00
-- url     : https://prove2.me/submissions/05d0a648-7acb-4072-8180-7f5b7cdcea04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_nonneg_a218ca485846

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) (T : Finset (Fin k))
    (u : Fin k × Fin n → ℂ) (hu : u ∈ polydisc _ C) : normT h T u ∈ polydisc _ C := by
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right] at hu ⊢
  intro ij
  by_cases hT : ij.1 ∈ T
  · simp only [normT, hT, if_true, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (h.li_norm_nonneg _)]
    by_cases h0 : (h.norm fun j => u (ij.1, j)) = 0
    · rw [h0, _root_.inv_zero, zero_mul]; exact hC0
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (h.li_norm_nonneg _) (Ne.symm h0))]
      have := hC (fun j => u (ij.1, j)) ij.2
      simpa [mul_comm] using this
  · simp only [normT, hT, if_false]
    exact hu ij
end GroundTheory.Heights₂.Heights.LogInt
