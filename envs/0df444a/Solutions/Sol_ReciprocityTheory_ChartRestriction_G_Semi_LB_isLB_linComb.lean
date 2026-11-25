-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:25.097874+00:00
-- url     : https://prove2.me/submissions/de643428-eaa1-4853-b962-d29d4477db6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_cocycle

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (LinComb L φ ε).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    choose j hj using fun k => mem_of_cover hL ((φ k).base y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  g_self := lcg_self hL φ ε
  cocycle := lcg_cocycle hL φ ε
end ReciprocityTheory.ChartRestriction.G.Semi.LB
