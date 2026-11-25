-- Prove2me | solution 1 for PI.SqfRootShift.W.arith1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:48.405544+00:00
-- url     : https://prove2.me/submissions/98ada584-2876-4cd0-9cb8-ce38a9e59192

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Theorems.Thm_PI_SqfRootShift_W_sum_le_prod_of_two_le
import Theorems.Thm_PI_SqfRootShift_W_le_pp
import Theorems.Thm_PI_SqfRootShift_W_two_le_pp
import Theorems.Thm_PI_SqfRootShift_W_prod_pp

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
theorem _root_.solution {n q d : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hd : d.Prime) (hqd : q ≠ d)
    (hq16 : 16 ≤ q) (hd16 : 16 ≤ d) (h16 : 16 ∣ n) (hqn : q ∣ n) (hdn : d ∣ n) :
    4 * min q d * ppSum n ≤ n := by
  classical
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (by norm_num : 2 ∣ 16).trans h16, hn⟩
  have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
  have hdmem : d ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn⟩
  have hq1 : q ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by omega, hqmem⟩
  have hd1 : d ∈ (n.primeFactors.erase 2).erase q :=
    Finset.mem_erase.mpr ⟨Ne.symm hqd, Finset.mem_erase.mpr ⟨by omega, hdmem⟩⟩
  have hsub : ((n.primeFactors.erase 2).erase q).erase d ⊆ n.primeFactors := fun p hp => by
    simp only [Finset.mem_erase] at hp; exact hp.2.2.2
  have hsum : ppSum n = 2 ^ n.factorization 2 + (q ^ n.factorization q + (d ^ n.factorization d +
      ∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p)) := by
    unfold ppSum
    rw [← Finset.add_sum_erase _ _ h2mem, ← Finset.add_sum_erase _ _ hq1,
      ← Finset.add_sum_erase _ _ hd1]
  have hprod : n = 2 ^ n.factorization 2 * (q ^ n.factorization q * (d ^ n.factorization d *
      ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p)) := by
    have h0 := prod_pp hn
    rw [← Finset.mul_prod_erase _ _ h2mem, ← Finset.mul_prod_erase _ _ hq1,
      ← Finset.mul_prod_erase _ _ hd1] at h0
    exact h0.symm
  have hR := sum_le_prod_of_two_le (((n.primeFactors.erase 2).erase q).erase d)
    (fun p => p ^ n.factorization p) (fun p hp => two_le_pp (hsub hp))
  have hPi : 0 < ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p :=
    prod_pos (fun p hp => by have := two_le_pp (hsub hp); omega)
  have hA : 16 ≤ 2 ^ n.factorization 2 := by
    have h4 : 4 ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp (by simpa using h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) h4
  have hB : q ≤ q ^ n.factorization q := le_pp hqmem
  have hC : d ≤ d ^ n.factorization d := le_pp hdmem
  have hm1 : min q d ≤ q := min_le_left _ _
  have hm2 : min q d ≤ d := min_le_right _ _
  rw [hsum]
  generalize 2 ^ n.factorization 2 = A at hprod hA ⊢
  generalize q ^ n.factorization q = B at hprod hB ⊢
  generalize d ^ n.factorization d = C at hprod hC ⊢
  generalize ∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = R at hR ⊢
  generalize ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = P
    at hprod hR hPi ⊢
  generalize min q d = m at hm1 hm2 ⊢
  subst hprod
  have e1 : 16 * (m * A) ≤ A * (B * (C * P)) := by
    calc 16 * (m * A) ≤ C * (B * A) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e2 : 16 * (m * B) ≤ A * (B * (C * P)) := by
    calc 16 * (m * B) ≤ A * (C * B) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e3 : 16 * (m * C) ≤ A * (B * (C * P)) := by
    calc 16 * (m * C) ≤ A * (B * C) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e4 : 16 * (4 * (m * R)) ≤ A * (B * (C * P)) := by
    calc 16 * (4 * (m * R)) ≤ A * (C * (B * P)) :=
          Nat.mul_le_mul hA (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hR))
      _ = A * (B * (C * P)) := by ring
  nlinarith
end PI.SqfRootShift.W
