-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.fam_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:13.790783+00:00
-- url     : https://prove2.me/submissions/5cdf884e-87b7-49fc-ac61-9b4d1379f776

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_psum_eq_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_comp_prod

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
open Semi
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
theorem _root_.solution {T : Over S} (a : T ⟶ G3 H) {m : ℕ} (y : Fin m → (T ⟶ H))
    (A : Fin 3 → Finset (Fin m)) (hA : ∀ i, a ≫ x3 H i = ∏ j ∈ A i, y j)
    (hdis : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) (k : thK) :
    a.left ≫ thφ H (x3 H) k = (∏ j ∈ k.down.biUnion A, y j).left := by
  classical
  show a.left ≫ (psum H (x3 H) k.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod, Finset.prod_biUnion]
  · exact congrArg Over.Hom.left (Finset.prod_congr rfl fun i _ => hA i)
  · intro i _ i' _ hii'
    exact hdis i i' hii'
end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
