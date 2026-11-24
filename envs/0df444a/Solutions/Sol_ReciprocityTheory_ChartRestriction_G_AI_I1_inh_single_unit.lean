-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_single_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:02.505923+00:00
-- url     : https://prove2.me/submissions/f6f1eaed-168a-4f41-a5ce-5ec4ee28c0ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (m : ℕ) : (Pi.single () m : Unit → ℕ) = fun _ => m := by
  funext u; cases u; simp
end ReciprocityTheory.ChartRestriction.G.AI.I1
