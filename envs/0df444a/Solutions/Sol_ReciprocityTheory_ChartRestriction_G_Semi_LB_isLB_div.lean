-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:45.085804+00:00
-- url     : https://prove2.me/submissions/dd25e89b-a3ee-45c1-8eca-edfaf2a1878b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_dg_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_dg_cocycle

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
theorem _root_.solution {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) : (div M L).IsLB where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := mem_of_cover hM x
    obtain ⟨j, hj⟩ := mem_of_cover hL x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
  g_self := dg_self hM hL
  cocycle := dg_cocycle hM hL
end ReciprocityTheory.ChartRestriction.G.Semi.LB
