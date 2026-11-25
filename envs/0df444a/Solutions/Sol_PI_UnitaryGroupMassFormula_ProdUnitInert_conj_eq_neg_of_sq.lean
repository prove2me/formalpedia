-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.conj_eq_neg_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:54.878443+00:00
-- url     : https://prove2.me/submissions/07ddfcdd-2966-41c5-9017-6e4a64207fe5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_ExistsRatCoords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) β = -β := by
  have h1 := congrArg Complex.re hβ
  have h2 := congrArg Complex.im hβ
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hre : β.re = 0 := by
    have hri : β.re * β.im = 0 := by linarith
    rcases mul_eq_zero.mp hri with h | h
    · exact h
    · rw [h] at h1
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [sq_nonneg β.re]
  apply Complex.ext <;> simp [hre]
end PI.UnitaryGroupMassFormula.ProdUnitInert
