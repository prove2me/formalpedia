-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_eq_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:49.202936+00:00
-- url     : https://prove2.me/submissions/c0339f4f-5a81-4d87-a56f-a85a7026d572

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne

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
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W)
    {S : Finset (σ →₀ ℕ)} (hS : P.support ⊆ S) :
    polyDeriv P u F x = ∑ m ∈ S, P.coeff m * pdTerm u F x m := by
  unfold polyDeriv
  refine Finset.sum_subset hS fun m _ hm => ?_
  first
    | rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.1 hm, zero_mul]
end ReciprocityTheory.ChartRestriction.G.I2
