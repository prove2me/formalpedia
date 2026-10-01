-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.dichotomy_ord_yukon_43a65ecb6294
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:26.579008+00:00
-- url     : https://prove2.me/submissions/eaa0a979-bfd3-46f9-86e1-743b314baf60

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


import Init
import Definitions.Def_Yukon_590a300e51c847902c7c8694
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
/-- Additive form of the dichotomy when `ord (D₀ F) = h`. -/
theorem _root_.solution (n₁ : ℕ) (h : ℤ) (x : ℤᵐ⁰) (hx : x = exp (-h))
    (hd : n₁ ≤ 1 ∨ x ^ 2 ≤ exp (-(3 * n₁ : ℤ))) : n₁ ≤ 1 ∨ 3 * (n₁ : ℤ) ≤ 2 * h  := by
  rcases hd with hd | hd
  · exact Or.inl hd
  · right
    rw [hx, sq, ← exp_add, exp_le_exp] at hd
    omega
end HFree6812
end SubmissionLower
end ProximityPrize
