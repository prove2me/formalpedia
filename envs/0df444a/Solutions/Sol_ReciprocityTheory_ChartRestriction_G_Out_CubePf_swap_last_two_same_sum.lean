-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.swap_last_two_same_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:16.928805+00:00
-- url     : https://prove2.me/submissions/aea1bb15-155e-460d-8640-61919f7a93e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_sameSum_of_factor_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_fam_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_th_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_swapLastTwo_proj_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_swapLastTwo_fiber_sum

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
open Semi CubeCoordinateSums
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution :
    LB.SameSum (thφ H (x3 H)) thε
      (fun k => (lift (x3 H 0) (lift (x3 H 2) (x3 H 1))).left ≫ thφ H (x3 H) k) thε := by
  classical
  have h1 : thφ H (x3 H) = fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) k.down :=
    funext fun k => th_eq H k
  have h2 : (fun k => (lift (x3 H 0) (lift (x3 H 2) (x3 H 1))).left ≫ thφ H (x3 H) k) =
      fun k => (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left) (k.down.biUnion swapLastTwoSubsets) :=
    funext fun k => fam_eq H _ (x3 H) swapLastTwoSubsets (swapLastTwo_proj_prod H) (by decide) k
  rw [h2, h1]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 3) => (∏ l ∈ J, x3 H l).left)
    (fun k : thK => k.down) (fun k : thK => k.down.biUnion swapLastTwoSubsets) thε thε swapLastTwo_fiber_sum
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
