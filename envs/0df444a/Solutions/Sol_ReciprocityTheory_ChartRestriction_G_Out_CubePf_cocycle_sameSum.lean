-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.cocycle_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:43.388967+00:00
-- url     : https://prove2.me/submissions/fc0161bd-0162-4780-802c-d1fda964195d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_sameSum_of_factor_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_fam_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_cubeFaceFirst_proj_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_cubeFaceOmit_proj_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_cubeFaceMiddle_proj_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_cubeFaceLast_proj_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_coc_fib

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
    LB.SameSum
      (Sum.elim (fun k => (lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 0) (lift (x4 H 1) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε)
      (Sum.elim (fun k => (lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 1) (lift (x4 H 2) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε) := by
  classical
  have h1 : Sum.elim (fun k => (lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 0) (lift (x4 H 1) (x4 H 3))).left ≫ thφ H (x3 H) k) =
      fun s => (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left)
        (Sum.elim (fun k : thK => k.down.biUnion c1A) (fun k : thK => k.down.biUnion c2A) s) := by
    funext s
    rcases s with k | k
    · exact fam_eq H _ (x4 H) c1A (cubeFaceFirst_proj_prod H) (by decide) k
    · exact fam_eq H _ (x4 H) c2A (cubeFaceOmit_proj_prod H) (by decide) k
  have h2 : Sum.elim (fun k => (lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 1) (lift (x4 H 2) (x4 H 3))).left ≫ thφ H (x3 H) k) =
      fun s => (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left)
        (Sum.elim (fun k : thK => k.down.biUnion c3A) (fun k : thK => k.down.biUnion c4A) s) := by
    funext s
    rcases s with k | k
    · exact fam_eq H _ (x4 H) c3A (cubeFaceMiddle_proj_prod H) (by decide) k
    · exact fam_eq H _ (x4 H) c4A (cubeFaceLast_proj_prod H) (by decide) k
  rw [h1, h2]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 4) => (∏ l ∈ J, x4 H l).left) _ _ _ _ coc_fib
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
