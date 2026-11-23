-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_monomial_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:51.773856+00:00
-- url     : https://prove2.me/submissions/7ed9e13b-2f1b-4a92-ad60-5b57ed693d70

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
theorem _root_.solution (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x = pdTerm u F x m := by
  classical
  rw [polyDeriv_eq_of_subset _ u F x (S := {m}) MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
end ReciprocityTheory.ChartRestriction.G.I2
