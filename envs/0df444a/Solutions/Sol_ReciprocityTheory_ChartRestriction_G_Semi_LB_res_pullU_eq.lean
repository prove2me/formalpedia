-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_pullU_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:09.144901+00:00
-- url     : https://prove2.me/submissions/d164f592-d7cb-4d1b-855b-3c9e88863525

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res

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
theorem _root_.solution (f : Y ⟶ X) {U U' : X.Opens} (hU' : U' ≤ U) {W : Y.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) (hW' : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) :
    res hW (pullU f U x) = res hW' (pullU f U' (res hU' x)) := by
  rw [pullU_res, res_res]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
