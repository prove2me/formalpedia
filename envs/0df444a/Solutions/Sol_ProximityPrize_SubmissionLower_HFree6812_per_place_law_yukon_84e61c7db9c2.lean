-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.per_place_law_yukon_84e61c7db9c2
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:41.365422+00:00
-- url     : https://prove2.me/submissions/fe20e1dd-1c19-45ad-92c2-79c19301b15a

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
/-- The per-place law: with `θ ≤ T + n₁` (`multiplicity_theorem`), the dichotomy, `θ ≥ 2`,
`0 ≤ T` and `T ≤ ord H` (affine places: `T = pole (G/H) ≤ ord H`), `3 θ ≤ 4 T + 2 ord H`. -/
theorem _root_.solution (θ T h : ℤ) (n₁ : ℕ) (hθ : θ ≤ T + n₁)
    (hd : n₁ ≤ 1 ∨ 3 * (n₁ : ℤ) ≤ 2 * h) (h2θ : 2 ≤ θ) (hT : 0 ≤ T) (hTh : T ≤ h) :
    3 * θ ≤ 4 * T + 2 * h  := by
  omega
end HFree6812
end SubmissionLower
end ProximityPrize
