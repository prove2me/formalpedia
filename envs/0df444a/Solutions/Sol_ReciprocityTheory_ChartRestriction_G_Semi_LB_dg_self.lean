-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:41.997002+00:00
-- url     : https://prove2.me/submissions/ad364587-0e2b-48cf-97b8-3fd89b11c253

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_g_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg

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
theorem _root_.solution {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p : M.ι × L.ι) :
    res (le_inf le_rfl le_rfl : M.U p.1 ⊓ L.U p.2 ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U p.1 ⊓ L.U p.2))
      (dg M L p p) = 1 := by
  rw [res_dg, res_g_self hM, res_g_self hL, inv_one, mul_one]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
