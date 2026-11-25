-- Prove2me | solution 1 for PI.KerFourSqW.rat_sum_four_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:49.600494+00:00
-- url     : https://prove2.me/submissions/1a12d4a8-4cba-48c9-8c9e-78e69632938c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW
namespace PI.KerFourSqW
theorem _root_.solution (a : ℚ) (ha : 0 < a) :
    ∃ r₁ r₂ r₃ r₄ : ℚ, r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 = a := by
  obtain ⟨s₁, s₂, s₃, s₄, hs⟩ := Nat.sum_four_squares (a.num.toNat * a.den)
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have hden : (0 : ℚ) < a.den := by exact_mod_cast a.pos
  refine ⟨s₁ / a.den, s₂ / a.den, s₃ / a.den, s₄ / a.den, ?_⟩
  have hcast : ((a.num.toNat * a.den : ℕ) : ℚ) = (a.num : ℚ) * a.den := by
    push_cast
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have h1 : ((s₁ : ℚ) ^ 2 + (s₂ : ℚ) ^ 2 + (s₃ : ℚ) ^ 2 + (s₄ : ℚ) ^ 2) = (a.num : ℚ) * a.den := by
    rw [← hcast]; exact_mod_cast hs
  rw [div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div, ← add_div, h1, pow_two, ← div_div,
    mul_div_cancel_right₀ _ hden.ne', Rat.num_div_den]
end PI.KerFourSqW
