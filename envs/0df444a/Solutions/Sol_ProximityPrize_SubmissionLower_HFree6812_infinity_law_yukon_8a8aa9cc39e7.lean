-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.infinity_law_yukon_8a8aa9cc39e7
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:29.424388+00:00
-- url     : https://prove2.me/submissions/2cba9069-be52-4be0-bfe0-7a5b50c88680

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
/-- The law at a place at infinity (`θ ≤ T`, `h ≥ 0`). -/
theorem _root_.solution (θ T h : ℤ) (hθ : θ ≤ T) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    3 * θ ≤ 4 * T + 2 * h  := by
  omega
end HFree6812
end SubmissionLower
end ProximityPrize
