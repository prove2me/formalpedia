-- Prove2me | solution 1 for QAlgorithms.Childs.periodFindingReals_convergent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:21:23.060448+00:00
-- url     : https://prove2.me/submissions/9180a3c9-e93b-4064-80c1-7173bf128dcc

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

private lemma rounded_large (r t a : ℝ) (hr : 1 < r) (ht : 3 * r ≤ t)
    (ha : 1 ≤ a) : r < (round (a * t) : ℝ) ∧ 2 * r * a < (round (a * t) : ℝ) := by
  have hround := abs_le.mp (abs_sub_round (a * t))
  have hat : 3 * r * a ≤ a * t := by nlinarith
  have hra : r ≤ r * a := by nlinarith
  constructor <;> nlinarith

private lemma rounded_cross (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(round (a * t) : ℝ) * b - a * (round (b * t) : ℝ)| ≤ (a + b) / 2 := by
  have ea := abs_le.mp (abs_sub_round (a * t))
  have eb := abs_le.mp (abs_sub_round (b * t))
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right ea.2 hb,
      mul_le_mul_of_nonneg_left eb.1 ha]
  · nlinarith [mul_le_mul_of_nonneg_right ea.1 hb,
      mul_le_mul_of_nonneg_left eb.2 ha]

theorem solution (r : ℝ) (N j j' : ℕ) (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hjr : (j : ℝ) < r) (hj'r : (j' : ℝ) < r) (hcop : Nat.Coprime j j')
    (hN : 3 * r ^ 2 ≤ (N : ℝ)) :
    (∃ n : ℕ, Real.convergent
        ((round ((j : ℝ) * N / r) : ℝ) / (round ((j' : ℝ) * N / r) : ℝ)) n =
        ((j : ℚ) / (j' : ℚ))) ∧
      |r - (round ((j : ℝ) * N / (round ((j : ℝ) * N / r) : ℝ)) : ℝ)| ≤ 1 := by
  have ha : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hb : (1 : ℝ) ≤ j' := by exact_mod_cast hj'
  have hr : 1 < r := ha.trans_lt hjr
  have hr0 : 0 < r := by linarith
  let t : ℝ := N / r
  have ht : 3 * r ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hr0).mpr
    nlinarith
  let A : ℝ := round ((j : ℝ) * t)
  let B : ℝ := round ((j' : ℝ) * t)
  have hA := rounded_large r t j hr ht ha
  have hB := rounded_large r t j' hr ht hb
  change r < A ∧ 2 * r * j < A at hA
  change r < B ∧ 2 * r * j' < B at hB
  have hA0 : 0 < A := hr0.trans hA.1
  have hB0 : 0 < B := hr0.trans hB.1
  have ha0 : (0 : ℝ) < j := by linarith
  have hb0 : (0 : ℝ) < j' := by linarith
  have hcross : |A * j' - (j : ℝ) * B| ≤ ((j : ℝ) + j') / 2 :=
    rounded_cross j j' t ha0.le hb0.le
  have hsep : ((j : ℝ) + j') * j' < B := by
    have h := mul_lt_mul_of_pos_right (show (j : ℝ) + j' < 2 * r by linarith) hb0
    nlinarith [hB.2]
  have herr : |A / B - (j : ℝ) / j'| < 1 / (2 * (j' : ℝ) ^ 2) := by
    have heq : A / B - (j : ℝ) / j' = (A * j' - (j : ℝ) * B) / (B * j') := by
      field_simp
    rw [heq, abs_div, abs_of_pos (mul_pos hB0 hb0)]
    apply (div_lt_iff₀ (mul_pos hB0 hb0)).mpr
    have hstrict : ((j : ℝ) + j') / 2 <
        (1 / (2 * (j' : ℝ) ^ 2)) * (B * j') := by
      have hm := mul_lt_mul_of_pos_right hsep hb0
      rw [one_div_mul_eq_div]
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (j' : ℝ) ^ 2)).mpr
      nlinarith
    exact hcross.trans_lt hstrict
  have hden : ((j : ℚ) / j').den = j' := by
    have h := Rat.den_div_eq_of_coprime (a := (j : ℤ)) (b := (j' : ℤ))
      (by exact_mod_cast (show 0 < j' by omega)) (by simpa using hcop)
    have h' : (((j : ℚ) / j').den : ℤ) = (j' : ℤ) := by
      simpa only [Int.cast_natCast] using h
    exact Int.natCast_inj.mp h'
  have hconv : ∃ n, Real.convergent (A / B) n = (j : ℚ) / j' := by
    obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent (ξ := A / B) (q := (j : ℚ) / j')
      (by simpa only [hden, Rat.cast_div, Rat.cast_natCast] using herr)
    exact ⟨n, hn.symm⟩
  constructor
  · simpa only [A, B, t, ← mul_div_assoc] using hconv
  · have hround := abs_sub_round ((j : ℝ) * N / A)
    have he : |r - (j : ℝ) * N / A| ≤ 1 / 2 := by
      have heq : r - (j : ℝ) * N / A = r * (A - (j : ℝ) * t) / A := by
        dsimp [t]
        field_simp
      rw [heq, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hA0]
      apply (div_le_iff₀ hA0).mpr
      have heA : |A - (j : ℝ) * t| ≤ 1 / 2 := by
        simpa only [A, abs_sub_comm] using abs_sub_round ((j : ℝ) * t)
      have := mul_le_mul_of_nonneg_left heA hr0.le
      linarith [hA.1]
    have htri := abs_add_le (r - (j : ℝ) * N / A)
      ((j : ℝ) * N / A - (round ((j : ℝ) * N / A) : ℝ))
    have hfinal : |r - (round ((j : ℝ) * N / A) : ℝ)| ≤ 1 := by
      rw [sub_add_sub_cancel] at htri
      linarith
    simpa only [A, t, ← mul_div_assoc] using hfinal
