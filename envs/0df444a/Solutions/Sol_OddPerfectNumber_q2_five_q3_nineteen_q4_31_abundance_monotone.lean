-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T00:08:18.214654+00:00
-- url     : https://prove2.me/submissions/72ce6d4d-a2af-42df-81f2-624a9c4eb93a

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_minimum_abundance_certificate
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two

theorem solution (a c e : Nat)
    (ha : 6 ≤ a) (hc : 2 ≤ c) (he : 2 ≤ e) :
    2 * (3 ^ a * 5 ^ 2 * 19 ^ c * 31 ^ e) <
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 31 ^ i) := by
  have sum_mono : ∀ {q n k : Nat}, n ≤ k →
      (∑ i ∈ Finset.range (n + 1), q ^ i) ≤
        (∑ i ∈ Finset.range (k + 1), q ^ i) := by
    intro q n k hnk
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.2 (Nat.succ_le_succ hnk)
    · intro i hi hnot
      exact Nat.zero_le _
  let S3 := ∑ i ∈ Finset.range (a + 1), 3 ^ i
  let S19 := ∑ i ∈ Finset.range (c + 1), 19 ^ i
  let S31 := ∑ i ∈ Finset.range (e + 1), 31 ^ i
  let P := 3 ^ a * 19 ^ c * 31 ^ e
  let S := S3 * S19 * S31
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_six a ha
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_two c hc
  have h31 := OddPerfectNumber.geom_ratio_lower_thirtyone_ge_two e he
  have h5 : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) = 31 := by
    norm_num [Finset.sum_range_succ]
  have hmul3 := Nat.mul_le_mul h3 h19
  have hmul31 := Nat.mul_le_mul hmul3 h31
  have hcross :
      (1093 * 381 * 993) * P ≤
        (729 * 361 * 961) * S := by
    simpa [P, S, S3, S19, S31, mul_assoc, mul_left_comm, mul_comm] using hmul31
  have hconst :
      2 * (25 * (729 * 361 * 961)) < (1093 * 381 * 993) * 31 := by
    norm_num
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hstrict :
      (2 * (25 * (729 * 361 * 961))) * P <
        ((1093 * 381 * 993) * 31) * P :=
    Nat.mul_lt_mul_of_pos_right hconst hPpos
  have hchain :
      (729 * 361 * 961) * (2 * (P * 25)) <
        (729 * 361 * 961) * (S * 31) := by
    calc
      (729 * 361 * 961) * (2 * (P * 25)) =
          (2 * (25 * (729 * 361 * 961))) * P := by ring
      _ < ((1093 * 381 * 993) * 31) * P := hstrict
      _ ≤ 31 * ((729 * 361 * 961) * S) := by
        calc
          ((1093 * 381 * 993) * 31) * P =
              31 * ((1093 * 381 * 993) * P) := by ring
          _ ≤ 31 * ((729 * 361 * 961) * S) :=
            Nat.mul_le_mul_left 31 hcross
      _ = (729 * 361 * 961) * (S * 31) := by ring
  have hdenpos : 0 < 729 * 361 * 961 := by norm_num
  have hfinal : 2 * (P * 25) < S * 31 :=
    (Nat.mul_lt_mul_left hdenpos).1 hchain
  simpa [P, S, S3, S19, S31, h5, mul_assoc, mul_left_comm, mul_comm] using hfinal
