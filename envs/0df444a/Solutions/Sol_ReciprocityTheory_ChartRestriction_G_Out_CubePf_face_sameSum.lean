-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.face_sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:07.68237+00:00
-- url     : https://prove2.me/submissions/4b7e205a-10bd-4918-a5a3-40da34b3ef39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_sameSum_of_factor_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_fam_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_face_hA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_face_hdis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_face_fib

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
theorem _root_.solution (i : Fin 3) :
    LB.SameSum (fun k : thK => (faceMap H i).left ≫ thφ H (x3 H) k) thε
      (PEmpty.elim : PEmpty → ((G2 H).left ⟶ H.left)) PEmpty.elim := by
  classical
  have hfam : (fun k : thK => (faceMap H i).left ≫ thφ H (x3 H) k) =
      fun k => (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left) (k.down.biUnion (faceA i)) :=
    funext fun k => fam_eq H (faceMap H i) (x2 H) (faceA i) (face_hA H i) (face_hdis i) k
  have hE : (PEmpty.elim : PEmpty → ((G2 H).left ⟶ H.left)) =
      fun k' => (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left) (PEmpty.elim k') :=
    funext fun k' => k'.elim
  rw [hfam, hE]
  exact sameSum_of_factor_loc (fun J : Finset (Fin 2) => (∏ l ∈ J, x2 H l).left)
    (fun k : thK => k.down.biUnion (faceA i)) (PEmpty.elim : PEmpty → Finset (Fin 2)) thε
    PEmpty.elim (face_fib i)
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
