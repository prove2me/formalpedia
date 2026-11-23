-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.pullU_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:42.844664+00:00
-- url     : https://prove2.me/submissions/912b07ac-f766-4503-9873-7741abcf3fea

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
theorem _root_.solution (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by
  ext; rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
