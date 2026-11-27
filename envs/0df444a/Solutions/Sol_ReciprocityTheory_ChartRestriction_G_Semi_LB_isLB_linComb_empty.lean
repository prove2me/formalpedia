-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:54.910442+00:00
-- url     : https://prove2.me/submissions/7d9263f8-0cc5-4ff4-b343-1fe5a43e9be1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_empty_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_empty_cocycle

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
theorem _root_.solution :
    (LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨PEmpty.elim, Set.mem_iInter.2 fun k => k.elim⟩
  g_self := lcg_empty_self L
  cocycle := lcg_empty_cocycle L
end ReciprocityTheory.ChartRestriction.G.Semi.LB
