-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_uDeg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:09:07.823339+00:00
-- url     : https://prove2.me/submissions/0a2e1a06-0129-4b49-9a37-4cfda8b6bbc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D N : ℕ} (s t : UXVar D N →₀ ℕ) : uDeg (s + t) = uDeg s + uDeg t := by
  unfold uDeg; simp [Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.T0
