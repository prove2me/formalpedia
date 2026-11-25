-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.gU_linCombIso_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:17:05.681884+00:00
-- url     : https://prove2.me/submissions/eaf4f199-ca81-4096-a3aa-1814de132351

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res'
  base_eq germ_pull germ_pull_pull germ_div)
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (φ₀ : Y ⟶ X)
    (p : (LB.LinComb M (K := PUnit) (fun _ => φ₀) (fun _ => 1)).ι ×
      (LB.LinComb L (K := PUnit) (fun _ => φ₀) (fun _ => 1)).ι) (y : Y)
    (hy : y ∈ (LB.div (LB.LinComb M (K := PUnit) (fun _ => φ₀) (fun _ => 1))
      (LB.LinComb L (K := PUnit) (fun _ => φ₀) (fun _ => 1))).U p)
    (hy' : y ∈ φ₀ ⁻¹ᵁ (LB.div M L).U (p.1 PUnit.unit, p.2 PUnit.unit)) :
    gU y hy ((LB.linCombIso w (K := PUnit) (fun _ => φ₀) (fun _ => 1)).s p) =
      gU y hy' (pullU φ₀ _ (w.s (p.1 PUnit.unit, p.2 PUnit.unit))) := by
  dsimp only [LB.linCombIso]
  first
  | erw [Fintype.prod_unique, zpow_one, gU_res]
  | simp only [Fintype.prod_unique, zpow_one, gU_res]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
