-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartCone_of_isWeightedHomogeneous_c74b1368637f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:51.524501+00:00
-- url     : https://prove2.me/submissions/af9386cc-1f2c-471d-8d30-213b31357cce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (D : Type*) [CommRing D] [Algebra (chartRing x c) D]
    {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} (hF : IsWeightedHomogeneous (coordDeg n) F d) :
    chartCone x c D F = C (algebraMap (chartRing x c) D (chartEval x c F)) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hF (mem_support_iff.mp hm)]
  have hε : chartEval x c (monomial m (coeff m F)) =
      algebraMap ℤ _ (coeff m F) * ∏ p, chartEval x c (X p) ^ m p := by
    rw [chartEval, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    simp only [aeval_X]
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι D) ^ m p = ∏ k, X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι D) ^ m ⟨k, i⟩ = _
    rw [← hm' k, Finset.prod_pow_eq_pow_sum]
  rw [hε, chartCone, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring
end GroundTheory.Heights₂.Heights.OrbitChartMult
