-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_g_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:58.590332+00:00
-- url     : https://prove2.me/submissions/97bc83ca-6a87-4931-83a8-fa2e43a31575

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_pullU_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_g_self

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι) {W : Y.Opens}
    (h : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i)) : res h (pullU f _ (L.g i i)) = 1 := by
  rw [res_pullU_eq f (le_refl (L.U i ⊓ L.U i)) h h, res_g_self hL i le_rfl, map_one, map_one]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
