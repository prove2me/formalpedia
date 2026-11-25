-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.gU_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:59:44.982852+00:00
-- url     : https://prove2.me/submissions/89837706-b90c-405e-9f5b-8b0d3168bd9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullU_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_lcg
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBxP
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')
variable {X X' Y Y' Z Z' : Scheme.{0}}
variable (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Out.LBxP
theorem _root_.solution (F : X' ⟶ X) (a : Y ⟶ X') (i j : PUnit → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((L.pull F).U i ⊓ (L.pull F).U j))
    (hy' : y ∈ (a ≫ F) ⁻¹ᵁ (L.U (i ⟨⟩) ⊓ L.U (j ⟨⟩))) :
    gU y hy (pullU a _ ((L.pull F).g i j)) = gU y hy' (pullU (a ≫ F) _ (L.g (i ⟨⟩) (j ⟨⟩))) := by
  rw [gU_pullU, gU_lcg L (fun _ => F) (fun _ => 1) i j (a.base y) hy]
  simp only [Fintype.prod_unique, zpow_one]
  exact (gU_pullU a _ y _ _).symm.trans (gU_pullU_comp a F _ _ y _ hy')
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
