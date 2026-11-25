-- Prove2me | solution 1 for PI.SqfRootShift.W.card_ppRoots_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:35.360601+00:00
-- url     : https://prove2.me/submissions/c42cfab4-2343-4701-8b71-75a5507454c6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
open Classical
namespace PI.SqfRootShift.W
theorem _root_.solution {K : Type*} [Field K] (N : ℕ) (hN : 2 ≤ N) :
    ((Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1)).card ≤ ppSum N := by
  have hN0 : 0 < N := by omega
  have hsub : (Polynomial.nthRootsFinset N (1 : K)).filter
      (fun y => ∃ ℓ, ℓ.Prime ∧ ∃ j, y ^ (ℓ ^ j) = 1) ⊆
      N.primeFactors.biUnion (fun p => Polynomial.nthRootsFinset (p ^ N.factorization p) (1 : K)) := by
    intro y hy
    rw [Finset.mem_filter, Polynomial.mem_nthRootsFinset hN0] at hy
    obtain ⟨hyN, ℓ, hℓ, j, hj⟩ := hy
    rw [Finset.mem_biUnion]
    have hdvd : orderOf y ∣ ℓ ^ j := orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
    have hoN : orderOf y ∣ N := orderOf_dvd_of_pow_eq_one hyN
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    ·
      have hy1 : y = 1 := by
        rw [h0, pow_zero, orderOf_eq_one_iff] at hoi; exact hoi
      refine ⟨N.minFac, ?_, ?_⟩
      · exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd N, by omega⟩
      · rw [Polynomial.mem_nthRootsFinset (pow_pos (Nat.minFac_pos N) _), hy1, one_pow]
    · have hℓN : ℓ ^ i ∣ N := hoi ▸ hoN
      have hmem : ℓ ∈ N.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hℓ, (dvd_pow_self ℓ hpos.ne').trans hℓN, by omega⟩
      refine ⟨ℓ, hmem, ?_⟩
      rw [Polynomial.mem_nthRootsFinset (pow_pos hℓ.pos _)]
      rw [← orderOf_dvd_iff_pow_eq_one, hoi]
      exact pow_dvd_pow ℓ ((hℓ.pow_dvd_iff_le_factorization (by omega)).1 hℓN)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  unfold ppSum
  refine Finset.sum_le_sum (fun p hp => ?_)
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
end PI.SqfRootShift.W
