-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.pullGen_pullAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:36.070181+00:00
-- url     : https://prove2.me/submissions/08174208-5ba5-4068-8b7c-1cee06f42b68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_rp_rp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gen_ext
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
theorem _root_.solution (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε))
    (a : Z ⟶ Y') (h2 : Z ⟶ Z') (b : Z' ⟶ Y) (hab : a ≫ h = h2 ≫ b)
    (hψ2 : ∀ k, (a ≫ ψ k) ≫ F = h2 ≫ (b ≫ φ k)) :
    LB.pullGen (L.pull F) ψ ε (GeneratorPullback.pullAlong L F h φ ε ψ hψ t) a =
      GeneratorPullback.pullAlong L F h2 (fun k => b ≫ φ k) ε (fun k => a ≫ ψ k) hψ2 (LB.pullGen L φ ε t b) := by
  apply gen_ext
  intro jj y hy
  exact (gU_rp_rp a h _ _ _ y hy).trans
    ((gU_pullU_congr hab _ _ y _ _).trans (gU_rp_rp h2 b _ _ _ y hy).symm)
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
