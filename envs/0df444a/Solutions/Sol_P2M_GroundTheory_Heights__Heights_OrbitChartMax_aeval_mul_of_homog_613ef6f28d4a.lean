-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_mul_of_homog_613ef6f28d4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:08.217833+00:00
-- url     : https://prove2.me/submissions/57c9aac5-e51d-469e-a38d-cbff90965b8f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax

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
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution {R : Type*} [CommRing R] [Algebra ℤ R] (t : ι → R) (z : Coord n → R)
    {G : MvPolynomial (Coord n) ℤ} {b : ι → ℕ} (hG : IsWeightedHomogeneous (coordDeg n) G b) :
    aeval (fun p ↦ t p.1 * z p) G = aeval z G * ∏ k, t k ^ b k := by
  classical
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmb : ∀ k, ∑ i, m ⟨k, i⟩ = b k := fun k ↦ by
    rw [← weight_coordDeg_apply, hG (mem_support_iff.mp hm)]
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hmb k]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (t k)
end GroundTheory.Heights₂.Heights.OrbitChartMax
