-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.sameSum_of_factor_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:43.190158+00:00
-- url     : https://prove2.me/submissions/d9fcdfac-10bc-47fd-b94a-91d69ca237c6

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
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
theorem _root_.solution {Y X : Scheme.{0}} {K K' J : Type} [Fintype K] [Fintype K']
    [Fintype J] [DecidableEq J] (P : J → (Y ⟶ X)) (f : K → J) (f' : K' → J) (ε : K → ℤ)
    (ε' : K' → ℤ)
    (h : ∀ j₀ : J, (∑ k, if f k = j₀ then ε k else 0) = ∑ k', if f' k' = j₀ then ε' k' else 0) :
    LB.SameSum (fun k => P (f k)) ε (fun k' => P (f' k')) ε' := by
  classical
  intro ψ
  have key : ∀ {L : Type} [Fintype L] (g : L → J) (δ : L → ℤ),
      (∑ k, if P (g k) = ψ then δ k else 0) =
        ∑ j, if P j = ψ then (∑ k, if g k = j then δ k else 0) else 0 := by
    intro L _ g δ
    calc (∑ k, if P (g k) = ψ then δ k else 0)
        = ∑ k, ∑ j, (if g k = j then (if P j = ψ then δ k else 0) else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_ite_eq Finset.univ (g k) (fun j => if P j = ψ then δ k else 0)]
          simp
      _ = ∑ j, ∑ k, (if g k = j then (if P j = ψ then δ k else 0) else 0) := Finset.sum_comm
      _ = ∑ j, if P j = ψ then (∑ k, if g k = j then δ k else 0) else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : P j = ψ
          · simp only [hj, if_true]
          · simp only [hj, if_false, ite_self, Finset.sum_const_zero]
  have e1 := key f ε
  have e2 := key f' ε'
  convert e1.trans ((Finset.sum_congr rfl fun j _ => by rw [h j]).trans e2.symm) using 2
end ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
