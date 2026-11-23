-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:08.544301+00:00
-- url     : https://prove2.me/submissions/a3667196-099f-4e27-b70c-930e048bd374

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) {h : W ≤ U} (x : Γ(X, U)ˣ) :
    res h x = res h₂ (res h₁ x) := by
  rw [res_res]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
