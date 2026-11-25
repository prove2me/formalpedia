-- Prove2me | solution 1 for PI.SqfRootShift.W.arith2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:07.216184+00:00
-- url     : https://prove2.me/submissions/86229dad-ce45-4500-841b-792f0b521543

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Theorems.Thm_PI_SqfRootShift_W_ppSum_le_self
import Theorems.Thm_PI_SqfRootShift_W_pp_lte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    ppSum (g ^ k - 1) ≤ k * ppSum (g - 1) + (g ^ k - 1) / (g - 1) := by
  classical
  have hdvd : g - 1 ∣ g ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 k
  have hgk : 2 ≤ g ^ k := le_trans hg (Nat.le_self_pow hk g)
  have hN0 : g ^ k - 1 ≠ 0 := by omega
  have hg0 : g - 1 ≠ 0 := by omega
  have hNS : g ^ k - 1 = (g - 1) * ((g ^ k - 1) / (g - 1)) := (Nat.mul_div_cancel' hdvd).symm
  have hS0 : (g ^ k - 1) / (g - 1) ≠ 0 := by
    intro h; rw [h, mul_zero] at hNS; exact hN0 hNS
  unfold ppSum
  rw [← Finset.sum_filter_add_sum_filter_not (g ^ k - 1).primeFactors (fun p => p ∣ g - 1)]
  refine add_le_add ?_ ?_
  · calc ∑ p ∈ (g ^ k - 1).primeFactors with p ∣ g - 1, p ^ (g ^ k - 1).factorization p
        ≤ ∑ p ∈ (g ^ k - 1).primeFactors with p ∣ g - 1, k * p ^ (g - 1).factorization p := by
          apply Finset.sum_le_sum; intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          exact pp_lte hp.1.1 hg h4 hp.2 hk
      _ ≤ ∑ p ∈ (g - 1).primeFactors, k * p ^ (g - 1).factorization p := by
          apply Finset.sum_le_sum_of_subset
          intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          rw [Nat.mem_primeFactors]; exact ⟨hp.1.1, hp.2, hg0⟩
      _ = k * ∑ p ∈ (g - 1).primeFactors, p ^ (g - 1).factorization p := by rw [Finset.mul_sum]
  · calc ∑ p ∈ (g ^ k - 1).primeFactors with ¬ p ∣ g - 1, p ^ (g ^ k - 1).factorization p
        = ∑ p ∈ (g ^ k - 1).primeFactors with ¬ p ∣ g - 1,
            p ^ ((g ^ k - 1) / (g - 1)).factorization p := by
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mem_filter] at hp
          conv_lhs => rw [hNS]
          rw [Nat.factorization_mul hg0 hS0, Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd hp.2, zero_add]
      _ ≤ ∑ p ∈ ((g ^ k - 1) / (g - 1)).primeFactors,
            p ^ ((g ^ k - 1) / (g - 1)).factorization p := by
          apply Finset.sum_le_sum_of_subset
          intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          rw [Nat.mem_primeFactors]
          refine ⟨hp.1.1, ?_, hS0⟩
          have h1 : p ∣ (g - 1) * ((g ^ k - 1) / (g - 1)) := hNS ▸ hp.1.2.1
          exact (hp.1.1.dvd_mul.mp h1).resolve_left hp.2
      _ ≤ (g ^ k - 1) / (g - 1) := ppSum_le_self hS0
end PI.SqfRootShift.W
