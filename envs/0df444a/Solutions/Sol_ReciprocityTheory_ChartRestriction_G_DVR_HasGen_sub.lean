-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:46.966118+00:00
-- url     : https://prove2.me/submissions/cb9802ef-61e4-40be-9e44-9e124321bf42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution {F G : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (hG : HasGen L G) : HasGen L (F - G) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
