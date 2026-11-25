-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:28.395289+00:00
-- url     : https://prove2.me/submissions/4daf8021-f8f0-4ca8-8165-da141809f55e

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
theorem _root_.solution (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : v y < 1)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = v y ^ m := by
  have h1 : v (y ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' hy (by omega)
  have h2 : v (1 + y ^ m) = v 1 :=
    Valuation.map_add_eq_of_lt_left v (by rw [map_one]; exact h1)
  rw [map_div₀, h2, map_one, div_one, map_pow]
end ReciprocityTheory.ChartRestriction.G.Lift.VA
