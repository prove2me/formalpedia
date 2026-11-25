-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:31.527019+00:00
-- url     : https://prove2.me/submissions/ecc7d890-2c01-48aa-b6ef-584be231873c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
variable {Ω : Type} [Field Ω]
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : 1 < v y)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = 1 := by
  have h1 : 1 < v (y ^ m) := by
    rw [map_pow]
    exact one_lt_pow' hy (by omega)
  have h2 : v (1 + y ^ m) = v (y ^ m) :=
    Valuation.map_add_eq_of_lt_right v (by rw [map_one]; exact h1)
  have h3 : v (y ^ m) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h1)
  rw [map_div₀, h2, div_self h3]
end ReciprocityTheory.ChartRestriction.G.Lift.VA
