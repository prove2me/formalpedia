-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_choose_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:14:06.238455+00:00
-- url     : https://prove2.me/submissions/8170ec7e-5e04-4533-919f-939dfddf715c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (D : ℕ) : StrictMono fun m : ℕ => (m + D + 1).choose (D + 1) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  show (m + D + 1).choose (D + 1) < (m + 1 + D + 1).choose (D + 1)
  rw [show m + 1 + D + 1 = (m + D + 1) + 1 by omega, Nat.choose_succ_succ' (m + D + 1) D]
  have := Nat.choose_pos (show D ≤ m + D + 1 by omega)
  omega
end ReciprocityTheory.ChartRestriction.G.T0
