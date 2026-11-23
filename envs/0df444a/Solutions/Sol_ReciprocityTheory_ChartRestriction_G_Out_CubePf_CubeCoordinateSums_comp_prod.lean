-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.comp_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:23.544303+00:00
-- url     : https://prove2.me/submissions/1db67c9f-b629-4d7f-bca6-de5a185bdc90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd

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
theorem _root_.solution {T T' : Over S} (a : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ H))
    (I : Finset (Fin n)) : a ≫ ∏ i ∈ I, x i = ∏ i ∈ I, (a ≫ x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact MonObj.comp_one a
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.prod_insert hb, MonObj.comp_mul, ih]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
