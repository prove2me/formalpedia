-- Prove2me | solution 1 for QuantumLTF.Majority.odd_krawtchouk_polynomial_witness
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:23:57.884002+00:00
-- url     : https://prove2.me/submissions/57078f62-95d4-42fa-b0aa-a36268a824ed

import Mathlib

namespace QuantumLTF.Majority

theorem odd_krawtchouk_polynomial_witness : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2)) ≤ C * Real.log r := by
  refine ⟨3, by norm_num, ?_⟩
  intro r hr hodd
  set s : ℝ := Real.sqrt (1/2) with hs
  have hss : s * s = 1/2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : s ^ 2 = 1/2 := by rw [sq, hss]
  have hr0 : (0 : Fin (r+1)) ≠ Fin.last r := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  let E : Fin (r+1) → Prop := fun t => t = 0 ∨ t = Fin.last r
  let p : Fin (r+1) → ℝ := fun t => if E t then s else 0
  let q : Fin (r+1) → ℝ := fun t => if E t then s else 1 / ((r.choose t : ℝ) * ((r : ℝ) + 1))
  have hE : ∀ t : Fin (r+1), ¬ E t → 1 ≤ (t : ℕ) ∧ (t : ℕ) < r := by
    intro t ht
    simp only [E, not_or] at ht
    obtain ⟨h0, hl⟩ := ht
    have h0' : (t : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simpa using h))
    have hl' : (t : ℕ) ≠ r := fun h => hl (Fin.ext (by simpa using h))
    have := t.isLt
    omega
  have hchpos : ∀ t : Fin (r+1), (0 : ℝ) < r.choose t := by
    intro t
    exact_mod_cast Nat.choose_pos (by have := t.isLt; omega)
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · simp [p, q, E, hss]
  · intro t h1 h2
    have hnE : ¬ E t := by
      simp only [E, not_or]
      constructor
      · intro h; subst h; simp at h1
      · intro h; subst h; simp at h2
    have hpos := hchpos t
    simp only [p, q, hnE, if_false]
    constructor
    · intro _
      have : (0:ℝ) < (r.choose t : ℝ) * ((r : ℝ) + 1) := by positivity
      exact (one_div_pos.mpr this).ne'
    · intro _; trivial
  · have hterm : ∀ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t) =
        (if t = 0 then 1/2 else 0) + (if t = Fin.last r then -1/2 else 0) := by
      intro t
      by_cases h0 : t = 0
      · subst h0
        simp [p, q, E, hss, Ne.symm hr0, hr0]
      by_cases hl : t = Fin.last r
      · subst hl
        have : (-1 : ℝ) ^ r = -1 := hodd.neg_one_pow
        simp [p, q, E, hss, Ne.symm hr0, this]
        ring
      · have hnE : ¬ E t := by simp [E, h0, hl]
        simp [p, hnE, h0, hl]
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num
  · have hterm : ∀ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2) ≤
        (if t = 0 then 1 else 0) + (if t = Fin.last r then 1 else 0) + 1 / ((r : ℝ) + 1) := by
      intro t
      have hr1 : (0:ℝ) < (r:ℝ) + 1 := by positivity
      have hinv : (0:ℝ) ≤ 1 / ((r:ℝ) + 1) := by positivity
      by_cases h0 : t = 0
      · subst h0
        simp [p, q, E, hs2, Ne.symm hr0, hr0]
        norm_num
        linarith
      by_cases hl : t = Fin.last r
      · subst hl
        simp [p, q, E, hs2, Ne.symm hr0]
        norm_num
        linarith
      · have hnE : ¬ E t := by simp [E, h0, hl]
        simp only [p, q, hnE, if_false, h0, hl]
        have hc := hchpos t
        have hc1 : (1:ℝ) ≤ r.choose t := by
          exact_mod_cast Nat.choose_pos (by have := t.isLt; omega)
        rw [show (r.choose t : ℝ) * ((0:ℝ) ^ 2 + (1 / ((r.choose t : ℝ) * ((r:ℝ) + 1))) ^ 2)
            = 1 / ((r.choose t : ℝ) * ((r:ℝ) + 1) ^ 2) by field_simp; ring]
        simp only [add_zero, zero_add]
        apply one_div_le_one_div_of_le hr1
        nlinarith
    calc (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2))
        ≤ ∑ t : Fin (r+1), ((if t = 0 then (1:ℝ) else 0) + (if t = Fin.last r then 1 else 0)
            + 1 / ((r : ℝ) + 1)) := Finset.sum_le_sum (fun t _ => hterm t)
      _ = 3 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
        simp
        field_simp
        ring
      _ ≤ 3 * Real.log r := by
        have hrpos : (0:ℝ) < r := by positivity
        have h1 : 1 ≤ Real.log r := by
          rw [Real.le_log_iff_exp_le hrpos]
          have := Real.exp_one_lt_d9
          have : (3:ℝ) ≤ r := by exact_mod_cast hr
          linarith
        linarith

end QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2)) ≤ C * Real.log r :=
  QuantumLTF.Majority.odd_krawtchouk_polynomial_witness
