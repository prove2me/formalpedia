-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.oneGen_pullAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:25.782051+00:00
-- url     : https://prove2.me/submissions/59d1d6f9-0c23-44d1-95ea-79752c4ac044

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gen_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_pullAlong
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
theorem _root_.solution (F : X' ⟶ X) (h : Y' ⟶ Y) (hψ : ∀ k : PEmpty, (PEmpty.elim k : Y' ⟶ X') ≫ F =
      h ≫ (PEmpty.elim k : Y ⟶ X)) :
    GeneratorPullback.pullAlong L F h PEmpty.elim PEmpty.elim PEmpty.elim hψ (LB.oneGen L) =
      LB.oneGen (L.pull F) := by
  apply gen_ext
  intro jj y hy
  refine (gU_pullAlong L F h PEmpty.elim PEmpty.elim PEmpty.elim hψ (LB.oneGen L) jj y hy).trans ?_
  exact ((congrArg (Units.map (h.stalkMap y).hom.toMonoidHom)
    (map_one (@gU Y (LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) (fun k => jj k ⟨⟩)) (h.base y)
      (GeneratorPullback.pullAlong_le L F h PEmpty.elim PEmpty.elim hψ jj hy)))).trans
    (map_one _)).trans (map_one (gU y hy)).symm
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
