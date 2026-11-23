-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_lcg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:16.450264+00:00
-- url     : https://prove2.me/submissions/d74cd1b1-69ef-4950-981d-54efc36a5e11

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
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) {W : Y.Opens}
    (hW : W ≤ wchart L φ j ⊓ wchart L φ j') :
    res hW (lcg L φ ε j j') =
      ∏ k, (res (hW.trans (wchart_inter_le L φ j j' k)) (pullU (φ k) _ (L.g (j k) (j' k)))) ^
        (ε k) := by
  rw [lcg, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (res_res _ _ _)
end ReciprocityTheory.ChartRestriction.G.Semi.LB
