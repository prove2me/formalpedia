-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_g_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:45.611709+00:00
-- url     : https://prove2.me/submissions/93117921-0354-42db-a13c-aeb97a7ce073

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_factor

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U i) :
    res h (L.g i i) = 1 := by
  rw [res_factor (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (h.trans inf_le_left),
    hL.g_self, map_one]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
