-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pull_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:43.678498+00:00
-- url     : https://prove2.me/submissions/21ccde43-8e7a-445a-aa92-46662018c097

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pull_g_eq
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
private theorem gU_pullU_comp_lemma (b : Z ⟶ Y) (a : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) (y : Z)
    (hy : y ∈ (b ≫ a) ⁻¹ᵁ U) :
    gU y hy (pullU (b ≫ a) U x) = gU y hy (pullU b (a ⁻¹ᵁ U) (pullU a U x)) := rfl
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
theorem _root_.solution (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (i j : PUnit.{1} → PUnit.{1} → L.ι) (y : Z)
    (hy : y ∈ ((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j)
    (hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))) :
    gU y hy (((L.pull a).pull b).g i j) =
      gU y hy' (pullU (b ≫ a) _ (L.g (i PUnit.unit PUnit.unit) (j PUnit.unit PUnit.unit))) := by
  rw [pull_g_eq (L.pull a) b i j, gU_res _ y hy, pull_g_eq L a (i PUnit.unit) (j PUnit.unit),
    gU_pullU_comp_lemma]
  exact gU_pullU_res _ _ _ _ _ _
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
