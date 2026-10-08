-- Prove2me | solution 1 for TalagrandConc.Chromatic.eq_9_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:24:10.525804+00:00
-- url     : https://prove2.me/submissions/c3cbab80-0acb-4fbe-a2fc-458f19670dc5

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical


namespace TalagrandConc.Chromatic

/-- ordered pairs `(i, j)` with `i < j` both in `s` -/
lemma card_lt_pairs {n : ℕ} (s : Finset (Fin n)) :
    2 * ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2)).card = s.card * s.card - s.card := by
  have hswap : ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
    apply Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap)
    · intro p _; simp
    · intro p _; simp
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s.offDiag) (p := fun p : Fin n × Fin n => p.1 < p.2)
  have h1 : s.offDiag.filter (fun p : Fin n × Fin n => p.1 < p.2)
      = (s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩; exact ⟨⟨h1, h2, ne_of_lt h4⟩, h4⟩
  have h2 : s.offDiag.filter (fun p : Fin n × Fin n => ¬ p.1 < p.2)
      = (s ×ˢ s).filter (fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, lt_of_le_of_ne (not_lt.mp h4) (Ne.symm h3)⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩; exact ⟨⟨h1, h2, ne_of_gt h4⟩, not_lt.mpr (le_of_lt h4)⟩
  rw [h1, h2, ← hswap, Finset.offDiag_card] at hsplit
  omega

lemma sum_edgeSlot_indicator {n : ℕ} (s : Finset (Fin n)) :
    (∑ e : EdgeSlot n, (if e.1.1 ∈ s ∧ e.1.2 ∈ s then (1 : ℝ) else 0))
      = ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (p := fun p : Fin n × Fin n => p.1 < p.2) (by simp)
      (fun p => if p.1 ∈ s ∧ p.2 ∈ s then (1 : ℝ) else 0)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  tauto

theorem eq_9_7_core {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r) :
    ((G.indepSetFinset r).card : ℝ)
      = ((r : ℝ) * ((r : ℝ) - 1) / 2)⁻¹ * ∑ e : EdgeSlot n, (indepCount G r e : ℝ) := by
  have hsum : ∑ e : EdgeSlot n, (indepCount G r e : ℝ)
      = ((G.indepSetFinset r).card : ℝ) * ((r : ℝ) * ((r : ℝ) - 1) / 2) := by
    have : ∀ e : EdgeSlot n, (indepCount G r e : ℝ)
        = ∑ s ∈ G.indepSetFinset r, (if e.1.1 ∈ s ∧ e.1.2 ∈ s then (1 : ℝ) else 0) := by
      intro e
      unfold indepCount
      rw [Finset.card_filter]; push_cast; rfl
    simp_rw [this]
    rw [Finset.sum_comm]
    have hs : ∀ s ∈ G.indepSetFinset r,
        (∑ e : EdgeSlot n, (if e.1.1 ∈ s ∧ e.1.2 ∈ s then (1 : ℝ) else 0))
          = (r : ℝ) * ((r : ℝ) - 1) / 2 := by
      intro s hs
      rw [SimpleGraph.mem_indepSetFinset_iff] at hs
      rw [sum_edgeSlot_indicator]
      have h := card_lt_pairs s
      rw [hs.card_eq] at h
      have hrr : r ≤ r * r := Nat.le_mul_self r
      have h' : (2 : ℝ) * ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2)).card
          = (r : ℝ) * r - r := by
        exact_mod_cast (by rw [h, Nat.cast_sub hrr]; push_cast; ring : ((2 * ((s ×ˢ s).filter (fun p : Fin n × Fin n => p.1 < p.2)).card : ℕ) : ℝ) = (r : ℝ) * r - r)
      linarith
    rw [Finset.sum_congr rfl hs, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hne : (r : ℝ) * ((r : ℝ) - 1) / 2 ≠ 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : (0:ℝ) < r - 1 := by linarith
    have h2 : (0:ℝ) < r := by linarith
    positivity
  field_simp
  have : (1 : ℝ) ≤ r - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  rw [mul_div_assoc, div_self (by linarith), mul_one]

end TalagrandConc.Chromatic

open TalagrandConc.Chromatic


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (hr : 2 ≤ r) :
    ((G.indepSetFinset r).card : ℝ)
      = ((r : ℝ) * ((r : ℝ) - 1) / 2)⁻¹ * ∑ e : EdgeSlot n, (indepCount G r e : ℝ) := by
  exact eq_9_7_core G r hr
