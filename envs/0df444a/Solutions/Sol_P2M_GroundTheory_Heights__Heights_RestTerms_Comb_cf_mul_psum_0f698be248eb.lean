-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:10.595389+00:00
-- url     : https://prove2.me/submissions/c0a46796-97ee-442f-93c6-2ca4de56a1e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_sum_377f06929651

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (l : Fin m → ℕ) (A : MvPolynomial (Fin m) ℚ) (q : ℕ) :
    cf l (A * psum (Fin m) ℚ q) =
      ∑ i, if q ≤ l i then cf (Function.update l i (l i - q)) A else 0 := by
  unfold psum
  rw [Finset.mul_sum, cf_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cf
  rw [X_pow_eq_monomial, coeff_mul_monomial', mul_one]
  have hle : Finsupp.single i q ≤ ex l ↔ q ≤ l i := by
    rw [Finsupp.single_le_iff]; simp
  by_cases h : q ≤ l i
  · rw [if_pos (hle.mpr h), if_pos h]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, Ne.symm hj]
  · rw [if_neg (fun h' => h (hle.mp h')), if_neg h]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
