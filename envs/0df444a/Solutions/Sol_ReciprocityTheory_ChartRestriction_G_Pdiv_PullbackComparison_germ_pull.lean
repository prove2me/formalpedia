-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:46.222969+00:00
-- url     : https://prove2.me/submissions/7dd6b0b3-6f51-4de7-9e64-27714a15d95c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
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
theorem _root_.solution (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) (y : Y)
    (hy : y ∈ (L.pull a).U i ⊓ (L.pull a).U j)
    (hy' : y ∈ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))) :
    gU y hy ((L.pull a).g i j) = gU y hy' (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := by
  rw [pull_g_lemma_6 L a i j]
  exact gU_res _ y hy _
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
