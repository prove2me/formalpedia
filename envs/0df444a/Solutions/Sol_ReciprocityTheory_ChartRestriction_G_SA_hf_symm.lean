-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hf_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:47.798303+00:00
-- url     : https://prove2.me/submissions/8b951ef8-a7a7-40da-ba2b-68d9552bb09e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (x y : ι → R) :
    σ (hf σ J x y) = hf σ J y x := by
  have hJ' : ∀ i j, σ (J i j) = J j i := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this
    exact this.symm
  simp only [hf, map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring
end ReciprocityTheory.ChartRestriction.G.SA
