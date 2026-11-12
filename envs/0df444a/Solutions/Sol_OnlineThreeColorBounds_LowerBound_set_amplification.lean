-- Prove2me | solution 1 for OnlineThreeColorBounds.LowerBound.set_amplification
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T14:08:40.876336+00:00
-- url     : https://prove2.me/submissions/cfc27b86-8c62-4d12-81ba-2254ee224c22

import Mathlib

set_option autoImplicit false

/-- Set amplification inequality: if `P` and `Q` are both at least `a` large and `X` is disjoint
from `P`, then one of `P ∪ Q`, `Q ∪ X` is at least `a + ⌈|X|/2⌉` large. -/
theorem solution {α : Type*} [DecidableEq α] (P Q X : Finset α) (a : ℝ) (t : ℕ)
    (hP : a ≤ (P.card : ℝ)) (hQ : a ≤ (Q.card : ℝ)) (hX : X.card = t)
    (hXP : Disjoint X P) :
    a + (((t + 1) / 2 : ℕ) : ℝ) ≤ (max (P ∪ Q).card (Q ∪ X).card : ℝ) := by
  classical
  set k : ℕ := (t + 1) / 2 with hk
  set K : ℕ := Nat.ceil a with hK
  have haK : a ≤ (K : ℝ) := Nat.le_ceil a
  have hKP : K ≤ P.card := Nat.ceil_le.mpr hP
  have hKQ : K ≤ Q.card := Nat.ceil_le.mpr hQ
  have hunion_eq : ((P ∪ Q) ∪ (Q ∪ X) : Finset α) = P ∪ Q ∪ X := by
    ext x
    simp only [Finset.mem_union]
    tauto
  have hnat' : P.card + Q.card + X.card ≤ (P ∪ Q).card + (Q ∪ X).card := by
    have hPX : (P ∪ X).card = P.card + X.card := Finset.card_union_of_disjoint hXP.symm
    have hsub1 : P ∪ X ⊆ P ∪ Q ∪ X := by
      intro x hx
      simp only [Finset.mem_union] at hx ⊢
      tauto
    have h1 : P.card + X.card ≤ (P ∪ Q ∪ X).card := by
      rw [← hPX]
      exact Finset.card_le_card hsub1
    have h2 : Q.card ≤ ((P ∪ Q) ∩ (Q ∪ X)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_union]
      exact ⟨Or.inr hx, Or.inl hx⟩
    have h4 : (P ∪ Q).card + (Q ∪ X).card =
        ((P ∪ Q) ∪ (Q ∪ X)).card + ((P ∪ Q) ∩ (Q ∪ X)).card := by
      have := Finset.card_union_add_card_inter (P ∪ Q) (Q ∪ X)
      omega
    calc P.card + Q.card + X.card = (P.card + X.card) + Q.card := by omega
      _ ≤ (P ∪ Q ∪ X).card + ((P ∪ Q) ∩ (Q ∪ X)).card := Nat.add_le_add h1 h2
      _ = ((P ∪ Q) ∪ (Q ∪ X)).card + ((P ∪ Q) ∩ (Q ∪ X)).card := by rw [hunion_eq]
      _ = (P ∪ Q).card + (Q ∪ X).card := h4.symm
  have hnat : P.card + Q.card + t ≤ (P ∪ Q).card + (Q ∪ X).card := by
    rw [← hX]
    exact hnat'
  by_contra hgoal
  push_neg at hgoal
  have hu_lt : ((P ∪ Q).card : ℝ) < a + (k : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast le_max_left (P ∪ Q).card (Q ∪ X).card) hgoal
  have hv_lt : ((Q ∪ X).card : ℝ) < a + (k : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast le_max_right (P ∪ Q).card (Q ∪ X).card) hgoal
  have hu_lt' : (P ∪ Q).card < K + k := by
    have h : ((P ∪ Q).card : ℝ) < (K : ℝ) + (k : ℝ) := by
      have := hu_lt
      linarith
    exact_mod_cast h
  have hv_lt' : (Q ∪ X).card < K + k := by
    have h : ((Q ∪ X).card : ℝ) < (K : ℝ) + (k : ℝ) := by
      have := hv_lt
      linarith
    exact_mod_cast h
  have hu1 : (P ∪ Q).card + 1 ≤ K + k := Nat.succ_le_of_lt hu_lt'
  have hv1 : (Q ∪ X).card + 1 ≤ K + k := Nat.succ_le_of_lt hv_lt'
  have hsum_ub : (P ∪ Q).card + (Q ∪ X).card ≤ 2 * K + 2 * k - 2 := by omega
  have hsum_lb : 2 * K + t ≤ (P ∪ Q).card + (Q ∪ X).card := by omega
  have h2k : 2 * k ≤ t + 1 := by
    rw [hk]
    exact Nat.mul_div_le (t + 1) 2
  omega
