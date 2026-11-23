-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:22.071883+00:00
-- url     : https://prove2.me/submissions/19cd4731-3954-4225-b7ed-660b41f6561e

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
theorem _root_.solution {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I = ∏ i ∈ I, x i := by
  classical
  have hf : ∀ l : List (Fin n), l.foldr (fun k acc => padd H (x k) acc) (pzero H T) =
      (l.map x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih]
      rfl
  unfold psum
  rw [hf, ← List.prod_toFinset x ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp
end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
