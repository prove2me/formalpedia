-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isGen_genPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:35:20.716136+00:00
-- url     : https://prove2.me/submissions/c42510e8-f670-4386-b194-8e448e35e19c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_ts_genPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull

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
theorem _root_.solution (M : LB X) (c : Gen M) (hc : c.IsGen) (f : Y ⟶ X) :
    (genPull M c f).IsGen := by
  refine (isGen_iff M _).2 fun i j => ?_
  have key := congrArg (fun x => res (wchart_pu_le M f i j) (pullU f _ x))
    (hc (i PUnit.unit) (j PUnit.unit))
  simp only [map_mul, pullU_res, res_res] at key
  rw [ts_genPull, ts_genPull, lcg_pull]
  simp only [res_res]
  exact key
end ReciprocityTheory.ChartRestriction.G.Semi.LB
