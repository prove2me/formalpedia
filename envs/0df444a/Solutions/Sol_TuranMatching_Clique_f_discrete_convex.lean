-- Prove2me | solution 1 for TuranMatching.Clique.f_discrete_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:41:07.732+00:00
-- url     : https://prove2.me/submissions/fa689d94-f1da-4312-8e5a-ae9576388fd7

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

set_option autoImplicit false
open Finset SimpleGraph
open TuranMatching.Clique

theorem tmk_two_choose (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem tmk_formula (k' q r : ℕ) (hr : r < k' + 1) :
    2 * turanNum ((k' + 1) * q + r) (k' + 1) + r = k' * q * (q * (k' + 1) + 2 * r) + r * r := by
  unfold turanNum
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  have hmod : ((k' + 1) * q + r) % (k' + 1) = r := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  rw [hmod]
  have h1 : ((k' + 1) * q + r) ^ 2 - r ^ 2 = (k' + 1) * (q * (q * (k' + 1) + 2 * r)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1]
  have h2 : (k' + 1) * (q * (q * (k' + 1) + 2 * r)) * (k' + 1 - 1) / (2 * (k' + 1)) =
      (q * (q * (k' + 1) + 2 * r) * k') / 2 := by
    have : (k' + 1) * (q * (q * (k' + 1) + 2 * r)) * (k' + 1 - 1) =
        (q * (q * (k' + 1) + 2 * r) * k') * (k' + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_mul_right _ _ (by omega : 0 < k' + 1)]
  rw [h2]
  have heven : Even (q * (q * (k' + 1) + 2 * r) * k') := by
    have : q * (q * (k' + 1) + 2 * r) * k' = q * q * (k' * (k' + 1)) + 2 * (q * r * k') := by ring
    rw [this]
    exact Even.add (Even.mul_left (Nat.even_mul_succ_self k') _) (even_two_mul _)
  have h3 := Nat.two_mul_div_two_of_even heven
  have h4 := tmk_two_choose r
  have h5 : q * (q * (k' + 1) + 2 * r) * k' = k' * q * (q * (k' + 1) + 2 * r) := by ring
  rw [h5] at h3 ⊢
  nlinarith

theorem tmk_incr (k' N : ℕ) :
    (turanNum (N + 1) (k' + 1) : ℤ) - turanNum N (k' + 1) = (N : ℤ) - ((N / (k' + 1) : ℕ) : ℤ) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < k' + 1 ∧ N = (k' + 1) * q + r :=
    ⟨N / (k' + 1), N % (k' + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod _ _).symm⟩
  have hq : ((k' + 1) * q + r) / (k' + 1) = q := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]
  rw [hq]
  have e1 := tmk_formula k' q r hr
  have e1' : (2 * (turanNum ((k' + 1) * q + r) (k' + 1) : ℤ) + r) =
      k' * q * (q * (k' + 1) + 2 * r) + r * r := by exact_mod_cast e1
  rcases Nat.lt_or_ge r k' with h | h
  · have e2 := tmk_formula k' q (r + 1) (by omega)
    have e2' : (2 * (turanNum ((k' + 1) * q + (r + 1)) (k' + 1) : ℤ) + (r + 1 : ℕ)) =
        k' * q * (q * (k' + 1) + 2 * (r + 1 : ℕ)) + (r + 1 : ℕ) * (r + 1 : ℕ) := by exact_mod_cast e2
    have : (k' + 1) * q + r + 1 = (k' + 1) * q + (r + 1) := by ring
    rw [this]
    push_cast at e2' ⊢
    nlinarith
  · have hrk : r = k' := by omega
    subst hrk
    have e2 := tmk_formula r (q + 1) 0 (by omega)
    have e2' : (2 * (turanNum ((r + 1) * (q + 1) + 0) (r + 1) : ℤ) + (0 : ℕ)) =
        r * (q + 1 : ℕ) * ((q + 1 : ℕ) * (r + 1) + 2 * (0 : ℕ)) + (0 : ℕ) * (0 : ℕ) := by exact_mod_cast e2
    have : (r + 1) * q + r + 1 = (r + 1) * (q + 1) + 0 := by ring
    rw [this]
    push_cast at e2' ⊢
    nlinarith

theorem tmk_div_le (k' N : ℕ) : N / (k' + 1) ≤ (N + 1) / (k' + 1) ∧ (N + 1) / (k' + 1) ≤ N / (k' + 1) + 1 := by
  constructor
  · exact Nat.div_le_div_right (by omega)
  · have : (N + 1) / (k' + 1) ≤ (N + (k' + 1)) / (k' + 1) := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ (by omega)] at this
    exact this

theorem tmk_turan_increment (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ((turanNum (N + 1) k : ℤ) - turanNum N k = (N : ℤ) - (N / k : ℕ)) ∧
    ((turanNum (N + 1) k : ℤ) - turanNum N k ≤ (turanNum (N + 2) k : ℤ) - turanNum (N + 1) k) ∧
    ((turanNum (N + 2) k : ℤ) - turanNum (N + 1) k ≤ (turanNum (N + 1) k : ℤ) - turanNum N k + 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e0 := tmk_incr k' N
  have e1 := tmk_incr k' (N + 1)
  obtain ⟨d1, d2⟩ := tmk_div_le k' N
  have d1' : ((N / (k' + 1) : ℕ) : ℤ) ≤ (((N + 1) / (k' + 1) : ℕ) : ℤ) := by exact_mod_cast d1
  have d2' : (((N + 1) / (k' + 1) : ℕ) : ℤ) ≤ ((N / (k' + 1) : ℕ) : ℤ) + 1 := by exact_mod_cast d2
  have h3 : N + 1 + 1 = N + 2 := rfl
  rw [h3] at e1
  refine ⟨e0, ?_, ?_⟩
  · rw [Nat.cast_succ] at e1; linarith
  · rw [Nat.cast_succ] at e1; linarith

theorem tmk_f_discrete_convex (n k s b : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (hb : b + 2 ≤ s - s / (k - 1)) :
    fCase4 n k s (b + 1) - fCase4 n k s b < fCase4 n k s (b + 2) - fCase4 n k s (b + 1) := by
  have hbs : b + 2 ≤ s := le_trans hb (Nat.sub_le _ _)
  obtain ⟨N, hN⟩ : ∃ N, 2 * s = b + 2 + N := ⟨2 * s - (b + 2), by omega⟩
  have e1 : 2 * s - b + 1 = N + 3 := by omega
  have e2 : 2 * s - (b + 1) + 1 = N + 2 := by omega
  have e3 : 2 * s - (b + 2) + 1 = N + 1 := by omega
  have hmono := (tmk_turan_increment k (by omega) (N + 1)).2.1
  have hN' : (2 * s : ℤ) = b + 2 + N := by exact_mod_cast hN
  unfold fCase4
  rw [e1, e2, e3]
  have h2 : N + 1 + 2 = N + 3 := rfl
  have h3 : N + 1 + 1 = N + 2 := rfl
  rw [h2, h3] at hmono
  push_cast
  nlinarith

theorem solution (n k s b : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (hb : b + 2 ≤ s - s / (k - 1)) :
    fCase4 n k s (b + 1) - fCase4 n k s b < fCase4 n k s (b + 2) - fCase4 n k s (b + 1) :=
  tmk_f_discrete_convex n k s b hk hn hb
