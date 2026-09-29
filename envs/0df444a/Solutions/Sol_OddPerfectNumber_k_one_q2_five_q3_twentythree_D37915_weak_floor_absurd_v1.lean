-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D37915_weak_floor_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T10:20:26.712321+00:00
-- url     : https://prove2.me/submissions/f6731319-b500-44fa-9d59-b0dd62c37393

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 3 ∨ D = 9 ∨ D = 15)
    (hp_eq : p = 2 * D - 1)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 292561 * 23 ^ (2*c) ≤
      279841 * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) := by
    omega
  have hsplit := Finset.sum_range_succ (fun i => q4 ^ i) (2*e)
  have hq : q4 ^ (2*e) ≤ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h23) hq
  -- NOTE: keep hmul's native left-associated shape; do not restate right-nested.
  have hcross := hmul
  have hS3 : 1 ≤ ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := by
    have h := Finset.single_le_sum (s := Finset.range (2*a + 1)) (f := fun i => 3 ^ i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0 < 2*a + 1))
    simpa using h
  have hS5 : 1 ≤ ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := by
    have h := Finset.single_le_sum (s := Finset.range (2*b + 1)) (f := fun i => 5 ^ i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0 < 2*b + 1))
    simpa using h
  have hS23 : 1 ≤ ∑ i ∈ Finset.range (2*c + 1), 23 ^ i := by
    have h := Finset.single_le_sum (s := Finset.range (2*c + 1)) (f := fun i => 23 ^ i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0 < 2*c + 1))
    simpa using h
  have hSq4 : 1 ≤ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i := by
    have h := Finset.single_le_sum (s := Finset.range (2*e + 1)) (f := fun i => q4 ^ i)
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0 < 2*e + 1))
    simpa using h
  have hsigpos : 0 < sigma := by
    rw [hsigma]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hS3 hS5) hS23) hSq4
  have hq4pos : 0 < q4 := by
    by_contra hz
    push_neg at hz
    have hq0 : q4 = 0 := by omega
    subst hq0
    have he2 : 2 * e ≠ 0 := by omega
    have hq0pow : (0:Nat) ^ (2*e) = 0 := zero_pow he2
    have hfac0 : m ^ 2 = 0 := by
      rw [hfac, hq0pow]
      simp
    have hm0 : m = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num : 2 ≠ 0) |>.mp hfac0
      exact this
    subst hm0
    simp at hrel
    rcases hD with rfl | rfl | rfl <;> simp at hrel <;> omega
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by positivity)) (by positivity))
      (pow_pos hq4pos _)
  have hbase : (9841 * 19531 * 292561) * D * (m ^ 2) ≤
      (6561 * 15625 * 279841) * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    have e1 : (9841 * 19531 * 292561) * D * (m ^ 2) =
        D * (9841 * 3 ^ (2*a) * (19531 * 5 ^ (2*b)) * (292561 * 23 ^ (2*c)) * q4 ^ (2*e)) := by
      rw [hfac]; ring
    have e2 : D * (6561 * (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
        (15625 * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i)) *
        (279841 * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i)) *
        (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) =
        (6561 * 15625 * 279841) * (D * sigma) := by rw [hsigma]; ring
    calc (9841 * 19531 * 292561) * D * (m ^ 2) = D * _ := e1
      _ ≤ D * _ := hmulD
      _ = (6561 * 15625 * 279841) * (D * sigma) := e2
      _ = (6561 * 15625 * 279841) * (p * (m ^ 2)) := by rw [hrel]
      _ = (6561 * 15625 * 279841) * p * (m ^ 2) := by ring
  rcases hD with rfl | rfl | rfl
  · have hp5 : p = 5 := by omega
    have hle : (9841 * 19531 * 292561) * 3 * (m ^ 2) ≤
        (6561 * 15625 * 279841) * 5 * (m ^ 2) := by simpa [hp5] using hbase
    have hrev : (6561 * 15625 * 279841) * 5 * (m ^ 2) <
        (9841 * 19531 * 292561) * 3 * (m ^ 2) := by
      have hc0 : (6561 * 15625 * 279841) * 5 < (9841 * 19531 * 292561) * 3 := by norm_num
      exact Nat.mul_lt_mul_of_pos_right hc0 hmpos
    exact False.elim ((Nat.not_lt_of_ge hle) hrev)
  · have hp17 : p = 17 := by omega
    have hle : (9841 * 19531 * 292561) * 9 * (m ^ 2) ≤
        (6561 * 15625 * 279841) * 17 * (m ^ 2) := by simpa [hp17] using hbase
    have hrev : (6561 * 15625 * 279841) * 17 * (m ^ 2) <
        (9841 * 19531 * 292561) * 9 * (m ^ 2) := by
      have hc0 : (6561 * 15625 * 279841) * 17 < (9841 * 19531 * 292561) * 9 := by norm_num
      exact Nat.mul_lt_mul_of_pos_right hc0 hmpos
    exact False.elim ((Nat.not_lt_of_ge hle) hrev)
  · have hp29 : p = 29 := by omega
    have hle : (9841 * 19531 * 292561) * 15 * (m ^ 2) ≤
        (6561 * 15625 * 279841) * 29 * (m ^ 2) := by simpa [hp29] using hbase
    have hrev : (6561 * 15625 * 279841) * 29 * (m ^ 2) <
        (9841 * 19531 * 292561) * 15 * (m ^ 2) := by
      have hc0 : (6561 * 15625 * 279841) * 29 < (9841 * 19531 * 292561) * 15 := by norm_num
      exact Nat.mul_lt_mul_of_pos_right hc0 hmpos
    exact False.elim ((Nat.not_lt_of_ge hle) hrev)
