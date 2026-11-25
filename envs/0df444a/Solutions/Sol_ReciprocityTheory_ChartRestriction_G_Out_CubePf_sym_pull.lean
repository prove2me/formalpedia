-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.sym_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:50:59.407636+00:00
-- url     : https://prove2.me/submissions/09089417-db84-4f57-bd2d-f9238465d099

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_symIso_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_sym_maps
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
theorem _root_.solution (L : RigLB G) (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen) :
    L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric := by
  intro h
  unfold RigLB.IsSymmetric at h ⊢
  obtain ⟨he, w, hw, hmaps⟩ := h
  exact ⟨eSec_inv G', symIso m L.L w, symIso_isGen m L.L w hw, sym_maps m L he w hmaps⟩
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
