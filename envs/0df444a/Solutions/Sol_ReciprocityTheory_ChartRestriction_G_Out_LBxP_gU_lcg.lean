-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBxP.gU_lcg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:03.915196+00:00
-- url     : https://prove2.me/submissions/28660918-8c34-41c3-8e36-af9a86e3dd12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) (y : Y)
    (hy : y ∈ (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j') :
    gU y hy ((LB.LinComb L φ ε).g j j') =
      ∏ k, (gU y (show y ∈ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) from
        ⟨LB.wchart_le L φ j k hy.1, LB.wchart_le L φ j' k hy.2⟩)
        (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k) := by
  have hy2 : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  have e : @Eq (Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ) ((LB.LinComb L φ ε).g j j')
      (∏ k, (@res Y (φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) (LB.wchart L φ j ⊓ LB.wchart L φ j')
        (le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k)))
        (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k)) := rfl
  show gU y hy2 _ = _
  rw [e, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact congrArg (· ^ ε k) (gU_res _ y hy2 _)
end ReciprocityTheory.ChartRestriction.G.Out.LBxP
