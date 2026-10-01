-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.sum_charge_le_yukon_936c0fd0929f
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:44.486183+00:00
-- url     : https://prove2.me/submissions/975cad92-845f-4893-a552-adcf78f24a99

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
/-- Summation over the places of a slice component: a charge `c` that satisfies the
per-place law at contributing places and vanishes elsewhere obeys
`3 Σ c ≤ 4 Σ T + 2 Σ h`. -/
theorem _root_.solution {ι : Type*} (W : Finset ι) (c T h : ι → ℤ)
    (hT : ∀ i ∈ W, 0 ≤ T i) (hh : ∀ i ∈ W, 0 ≤ h i)
    (hc : ∀ i ∈ W, c i = 0 ∨ 3 * c i ≤ 4 * T i + 2 * h i) :
    3 * ∑ i ∈ W, c i ≤ 4 * ∑ i ∈ W, T i + 2 * ∑ i ∈ W, h i  := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  rcases hc i hi with h0 | h1
  · have := hT i hi; have := hh i hi; rw [h0]; omega
  · exact h1
end HFree6812
end SubmissionLower
end ProximityPrize
