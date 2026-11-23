-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:30.750812+00:00
-- url     : https://prove2.me/submissions/8cbf9cf7-1050-4106-9053-70c2772504cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_eq_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (P + Q) u F x = polyDeriv P u F x + polyDeriv Q u F x := by
  classical
  rw [polyDeriv_eq_of_subset (P + Q) u F x (S := P.support ∪ Q.support) MvPolynomial.support_add,
    polyDeriv_eq_of_subset P u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_left _ h),
    polyDeriv_eq_of_subset Q u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]
end ReciprocityTheory.ChartRestriction.G.I2
