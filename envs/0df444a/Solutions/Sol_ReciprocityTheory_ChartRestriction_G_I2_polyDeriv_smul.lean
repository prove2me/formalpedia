-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:40.177821+00:00
-- url     : https://prove2.me/submissions/b7ed75bf-d1d3-4cad-95fe-8792364020a1

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
theorem _root_.solution (c : ℂ) (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (c • P) u F x = c * polyDeriv P u F x := by
  classical
  rw [polyDeriv_eq_of_subset (c • P) u F x (S := P.support) MvPolynomial.support_smul,
    polyDeriv_eq_of_subset P u F x (S := P.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2
