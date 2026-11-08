-- Prove2me | solution 1 for QBFBackdoor.round_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:47:37.994304+00:00
-- url     : https://prove2.me/submissions/187c86d2-366b-4de4-9a73-4df02b6b6ab3

import Mathlib
import Definitions.Def_QBFBackdoor_roundMap

namespace Aux_QBF_rounds
open QBFBackdoor

theorem r_le4 {d : ℕ} (h : d ≤ 4) : rounds d = 0 := by rw [rounds, dif_pos h]
theorem r_gt4 {d : ℕ} (h : ¬ d ≤ 4) : rounds d = rounds (roundMap d) + 1 := by
  rw [rounds, dif_neg h]

theorem p1 (d : ℕ) : 3 * roundMap d ≤ 2 * d + 5 := by
  unfold roundMap; split_ifs <;> omega

theorem p2 (d : ℕ) (h : 10 ≤ d) : 6 * roundMap d ≤ 5 * d := by
  unfold roundMap; split_ifs <;> omega

theorem p3 (d : ℕ) (h1 : 5 ≤ d) (h2 : d ≤ 9) : rounds d ≤ 3 := by
  interval_cases d
  · rw [r_gt4 (by norm_num), show roundMap 5 = 4 by decide, r_le4 (by norm_num)]; norm_num
  · rw [r_gt4 (by norm_num), show roundMap 6 = 4 by decide, r_le4 (by norm_num)]; norm_num
  · rw [r_gt4 (by norm_num), show roundMap 7 = 5 by decide, r_gt4 (by norm_num),
      show roundMap 5 = 4 by decide, r_le4 (by norm_num)]; norm_num
  · rw [r_gt4 (by norm_num), show roundMap 8 = 6 by decide, r_gt4 (by norm_num),
      show roundMap 6 = 4 by decide, r_le4 (by norm_num)]; norm_num
  · rw [r_gt4 (by norm_num), show roundMap 9 = 7 by decide, r_gt4 (by norm_num),
      show roundMap 7 = 5 by decide, r_gt4 (by norm_num), show roundMap 5 = 4 by decide,
      r_le4 (by norm_num)]

theorem small (d : ℕ) (h : d < 10) : rounds d ≤ 3 := by
  by_cases h4 : d ≤ 4
  · rw [r_le4 h4]; norm_num
  · exact p3 d (by omega) (by omega)

theorem steps : ∀ k d, 5 ^ k * d < 10 * 6 ^ k → rounds d ≤ k + 3 := by
  intro k
  induction k with
  | zero => intro d hd; simp at hd; exact small d hd
  | succ k ih =>
    intro d hd
    by_cases h10 : d < 10
    · exact (small d h10).trans (by omega)
    · push_neg at h10
      rw [r_gt4 (by omega)]
      have h6 := p2 d h10
      have : 5 ^ k * roundMap d < 10 * 6 ^ k := by
        have e1 : 5 ^ (k + 1) * d = 5 ^ k * (5 * d) := by ring
        have e2 : 10 * 6 ^ (k + 1) = 6 * (10 * 6 ^ k) := by ring
        rw [e1, e2] at hd
        have : 5 ^ k * (6 * roundMap d) ≤ 5 ^ k * (5 * d) := Nat.mul_le_mul_left _ h6
        nlinarith
      have := ih (roundMap d) this
      omega

end Aux_QBF_rounds

open QBFBackdoor Aux_QBF_rounds in
theorem solution :
    (∀ d, 3 * roundMap d ≤ 2 * d + 5) ∧
    (∀ d, 10 ≤ d → 6 * roundMap d ≤ 5 * d) ∧
    (∀ d, 5 ≤ d → d ≤ 9 → rounds d ≤ 3) ∧
    (∃ C : ℕ, ∀ d₀ : ℕ, rounds d₀ ≤ C * Nat.log 2 (d₀ + 1)) := by
  refine ⟨p1, p2, p3, 11, fun d₀ => ?_⟩
  set L := Nat.log 2 (d₀ + 1) with hL
  have hlt : d₀ + 1 < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hpow : 2 ^ (L + 1) * 625 ^ (L + 1) ≤ 1296 ^ (L + 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) _
  have hk : 5 ^ (4 * (L + 1)) * d₀ < 10 * 6 ^ (4 * (L + 1)) := by
    rw [pow_mul, pow_mul]
    norm_num
    have h1 : 625 ^ (L + 1) * d₀ < 625 ^ (L + 1) * 2 ^ (L + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    nlinarith
  have hr := steps _ _ hk
  by_cases hd : d₀ = 0
  · subst hd; rw [r_le4 (by norm_num)]; exact Nat.zero_le _
  · have hL1 : 1 ≤ L := by
      rw [hL]; apply Nat.le_log_of_pow_le (by norm_num); omega
    nlinarith
