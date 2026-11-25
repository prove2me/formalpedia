-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_coeff_eq_zero_of_distinct_roots_3974fe2d6676
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:26.910027+00:00
-- url     : https://prove2.me/submissions/02ead4d7-063e-4264-9057-cebf5a323280

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermNullstellensatz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
theorem _root_.solution {N : ℕ} (c t : Fin N → ℂ) (ht : Function.Injective t)
    (hroot : ∀ m, ∑ j, c j * t m ^ (j : ℕ) = 0) : ∀ j, c j = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun j => j.elim0
  set Q : Polynomial ℂ := ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
  have hQe : ∀ s, Q.eval s = ∑ j, c j * s ^ (j : ℕ) := by
    intro s
    simp [Q, Polynomial.eval_finsetSum]
  have hdeg : Q.natDegree < Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun j _ => ?_)
      (Nat.sub_lt hN Nat.one_pos)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hQ : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q ht
    (fun m => by rw [hQe]; exact hroot m) hdeg
  intro j
  have hj := congrArg (fun q : Polynomial ℂ => q.coeff (j : ℕ)) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Fin.val_inj] at hj
  simpa using hj
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
