-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:58.662352+00:00
-- url     : https://prove2.me/submissions/96fc8057-a7e0-4f85-bf76-bf63524a1094

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open ReciprocityTheory.ChartRestriction.G.Semi.LB
variable {X Y Z : Scheme.{u}}
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : Gen (LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ts (pullGen L φ ε c h) j = res (wchart_comp_le L h φ j) (pullU h _ (ts c j)) := rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
