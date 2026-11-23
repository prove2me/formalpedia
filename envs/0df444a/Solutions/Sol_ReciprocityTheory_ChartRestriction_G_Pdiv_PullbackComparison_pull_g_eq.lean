-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.pull_g_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:08.363787+00:00
-- url     : https://prove2.me/submissions/4ff24c58-01eb-498a-bda1-b28f9884c8af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
section Germs
end Germs
section Transfer
variable {X Y Z Y' : Scheme.{0}}
private theorem pull_g_lemma_6 (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).g i j = res (pull_le_lemma_5 L a i j) (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := by
  dsimp only [LB.pull, LB.LinComb]
  simp only [Fintype.prod_subsingleton _ PUnit.unit, zpow_one]
  first
  | rfl
  | skip
end Transfer
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).g i j = res (pull_inf_le L a i j) (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := pull_g_lemma_6 L a i j
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
