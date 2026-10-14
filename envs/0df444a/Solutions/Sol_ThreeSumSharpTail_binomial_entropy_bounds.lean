-- Prove2me | solution 1 for ThreeSumSharpTail.binomial_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T15:19:41.021436+00:00
-- url     : https://prove2.me/submissions/8fc67a26-7d4e-41b8-a8a1-95b11969eae3

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace ThreeSumSharpTail.Binomial

noncomputable def term (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

lemma term_nonneg (n j : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ term n p j := by
  unfold term
  positivity

lemma term_sum (n : ℕ) (p : ℝ) :
    ∑ j ∈ Finset.range (n + 1), term n p j = 1 := by
  have h := add_pow p (1 - p) n
  simp only [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  unfold term
  ring

lemma term_step (n j : ℕ) (p : ℝ) (hj : j < n) :
    term n p (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 - p) =
    term n p j * ((n - j : ℕ) : ℝ) * p := by
  have he : n - j = n - (j + 1) + 1 := by omega
  have hchoose : (n.choose (j + 1) : ℝ) * (j + 1 : ℕ) =
      (n.choose j : ℝ) * (n - j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  unfold term
  rw [he, pow_succ, pow_succ]
  rw [he] at hchoose
  calc
    _ = ((n.choose (j + 1) : ℝ) * (j + 1 : ℕ)) *
        (p ^ j * p * (1 - p) ^ (n - (j + 1)) * (1 - p)) := by ring
    _ = _ := by rw [hchoose]; ring

lemma mode (n k j : ℕ) (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    (hj : j ≤ n) : term n ((k : ℝ) / n) j ≤ term n ((k : ℝ) / n) k := by
  let p : ℝ := (k : ℝ) / n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < p := div_pos (by exact_mod_cast hk0) hnR
  have hp1 : p < 1 := (div_lt_one hnR).2 (by exact_mod_cast hkn)
  have hkp : (n : ℝ) * p = k := by dsimp [p]; field_simp
  have hu : ∀ i, i < k → term n p i ≤ term n p (i + 1) := by
    intro i hi
    have hin : i < n := hi.trans hkn
    have hdiff : ((n - i : ℕ) : ℝ) = n - i := Nat.cast_sub hin.le
    have hcoef : ((i + 1 : ℕ) : ℝ) * (1 - p) ≤ ((n - i : ℕ) : ℝ) * p := by
      rw [hdiff, Nat.cast_add, Nat.cast_one]
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      nlinarith
    have hstep := term_step n i p hin
    have hmul := mul_le_mul_of_nonneg_left hcoef (term_nonneg n i p hp.le hp1.le)
    apply (mul_le_mul_iff_left₀ (show 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) by positivity)).1
    nlinarith [hmul]
  have hd : ∀ i, k ≤ i → i < n → term n p (i + 1) ≤ term n p i := by
    intro i hki hin
    have hdiff : ((n - i : ℕ) : ℝ) = n - i := Nat.cast_sub hin.le
    have hcoef : ((n - i : ℕ) : ℝ) * p ≤ ((i + 1 : ℕ) : ℝ) * (1 - p) := by
      rw [hdiff, Nat.cast_add, Nat.cast_one]
      have : (k : ℝ) ≤ i := by exact_mod_cast hki
      nlinarith
    have hstep := term_step n i p hin
    have hmul := mul_le_mul_of_nonneg_left hcoef (term_nonneg n i p hp.le hp1.le)
    apply (mul_le_mul_iff_left₀ (show 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) by positivity)).1
    nlinarith [hmul]
  change term n p j ≤ term n p k
  by_cases hjk : j ≤ k
  · have hinc : ∀ l, j ≤ l → l ≤ k → term n p j ≤ term n p l := by
      intro l hjl hlk
      induction l, hjl using Nat.le_induction with
      | base => exact le_rfl
      | succ l hjl ih => exact (ih (by omega)).trans (hu l (by omega))
    exact hinc k hjk le_rfl
  · have hdec : ∀ l, k ≤ l → l ≤ n → term n p l ≤ term n p k := by
      intro l hkl hln
      induction l, hkl using Nat.le_induction with
      | base => exact le_rfl
      | succ l hkl ih => exact (hd l hkl (by omega)).trans (ih (by omega))
    exact hdec j (by omega) hj

end ThreeSumSharpTail.Binomial

theorem solution (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) :
    Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) / (r + 1) ≤
        (Nat.choose r k : ℝ) ∧
    (Nat.choose r k : ℝ) ≤
        Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hden : 0 < (r : ℝ) + 1 := by positivity
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_div, ThreeSumSharpTail.entropy, Real.log_zero,
      neg_zero, sub_zero, Real.log_one, mul_zero, Real.exp_zero,
      Nat.choose_zero_right, Nat.cast_one]
    constructor
    · apply (div_le_iff₀ hden).2
      linarith
    · exact le_rfl
  by_cases hkr : k = r
  · subst k
    simp only [div_self hrR.ne', ThreeSumSharpTail.entropy, Real.log_one,
      mul_zero, sub_self, Real.log_zero, Real.exp_zero,
      Nat.choose_self, Nat.cast_one]
    constructor
    · apply (div_le_iff₀ hden).2
      linarith
    · exact le_rfl
  have hk0' : 0 < k := by omega
  have hkr' : k < r := by omega
  let p : ℝ := (k : ℝ) / r
  let Q : ℝ := p ^ k * (1 - p) ^ (r - k)
  let E : ℝ := Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy p)
  have hp : 0 < p := div_pos (by exact_mod_cast hk0') hrR
  have hp1 : p < 1 := (div_lt_one hrR).2 (by exact_mod_cast hkr')
  have hkp : (r : ℝ) * p = k := by dsimp [p]; field_simp
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hlog : Real.log Q = -(r : ℝ) * ThreeSumSharpTail.entropy p := by
    dsimp [Q]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Nat.cast_sub hk, ← hkp]
    unfold ThreeSumSharpTail.entropy
    ring
  have hQE : Q * E = 1 := by
    calc
      Q * E = Real.exp (Real.log Q + (r : ℝ) * ThreeSumSharpTail.entropy p) := by
        rw [Real.exp_add, Real.exp_log hQ]
      _ = 1 := by rw [hlog]; simp
  have hsum := ThreeSumSharpTail.Binomial.term_sum r p
  have hupper : (r.choose k : ℝ) * Q ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := ThreeSumSharpTail.Binomial.term r p)
      (fun i hi => ThreeSumSharpTail.Binomial.term_nonneg r i p hp.le hp1.le)
      (show k ∈ Finset.range (r + 1) by simp; omega)
    rw [hsum] at h
    simpa [ThreeSumSharpTail.Binomial.term, Q, mul_assoc] using h
  have hlower : 1 ≤ ((r : ℝ) + 1) * ((r.choose k : ℝ) * Q) := by
    have h := Finset.sum_le_sum (s := Finset.range (r + 1))
      (f := ThreeSumSharpTail.Binomial.term r p)
      (g := fun _ => ThreeSumSharpTail.Binomial.term r p k) (by
        intro i hi
        apply ThreeSumSharpTail.Binomial.mode r k i (by omega) hk0' hkr'
        simpa using hi)
    rw [hsum] at h
    simpa [ThreeSumSharpTail.Binomial.term, Q, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h
  change E / ((r : ℝ) + 1) ≤ (r.choose k : ℝ) ∧ (r.choose k : ℝ) ≤ E
  constructor
  · apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_right hlower hE.le
    calc
      E = 1 * E := by ring
      _ ≤ (((r : ℝ) + 1) * ((r.choose k : ℝ) * Q)) * E := h
      _ = (r.choose k : ℝ) * ((r : ℝ) + 1) := by
        calc
          _ = (r.choose k : ℝ) * ((r : ℝ) + 1) * (Q * E) := by ring
          _ = _ := by rw [hQE]; ring
  · calc
      (r.choose k : ℝ) = ((r.choose k : ℝ) * Q) * E := by
        rw [mul_assoc, hQE, mul_one]
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right hupper hE.le
      _ = E := one_mul E

#print axioms solution
