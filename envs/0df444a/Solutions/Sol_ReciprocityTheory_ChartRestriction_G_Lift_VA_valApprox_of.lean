-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.valApprox_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:17:05.465709+00:00
-- url     : https://prove2.me/submissions/71ca2978-4912-4754-9579-a9d8c5693381

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution (hP : PairSep) (hL : LargeSmall) (hN : NearOne) (hA : Assembly) :
    ReciprocityTheory.ChartRestriction.G.Lift.ApproxStatement := by
  intro Ω _ ι _ v h1 hne n
  have h1' : ∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ) := h1
  have hgt : ∀ i, ∃ x, 1 < v i x := fun i => by
    obtain ⟨x, hx⟩ := h1' i
    refine ⟨x, ?_⟩
    rw [hx]
    first
    | exact WithZero.one_lt_exp_of_pos zero_lt_one
    | (rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; exact zero_lt_one)
    | exact WithZero.coe_lt_coe.2 (by decide)
  obtain ⟨x, hx⟩ := hA Ω ι v h1' (hN Ω ι v (hL Ω ι v hgt (hP Ω ι v h1' hne))) n
  exact ⟨x, hx⟩
end ReciprocityTheory.ChartRestriction.G.Lift.VA
