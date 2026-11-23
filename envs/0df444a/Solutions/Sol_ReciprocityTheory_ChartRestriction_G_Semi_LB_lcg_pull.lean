-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:28.750866+00:00
-- url     : https://prove2.me/submissions/104d1890-fda0-49c4-a456-759a25f8cfac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb

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
theorem _root_.solution (M : LB X) (f : Y ⟶ X) (i j : PUnit.{u+1} → M.ι) :
    lcg M (K := PUnit) (fun _ => f) (fun _ => 1) i j =
      res (wchart_pu_le M f i j) (pullU f _ (M.g (i PUnit.unit) (j PUnit.unit))) := by
  rw [lcg, Fintype.prod_unique, zpow_one]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
