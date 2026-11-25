-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_prod_pow_weight_36e2650dc969
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:35:48.044688+00:00
-- url     : https://prove2.me/submissions/2b100711-922e-432b-9c57-e00181772737

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution [Fintype ι] {F : Type*} [CommRing F] (u : ι → F) (m : Coord n →₀ ℕ) :
    (m.prod fun v e ↦ u v.1 ^ e) = ∏ k, u k ^ Finsupp.weight (coordDeg n) m k := by
  simp only [Finsupp.weight_apply, coordDeg, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp
end GroundTheory.Heights₂.Heights.BoundedMonomials
