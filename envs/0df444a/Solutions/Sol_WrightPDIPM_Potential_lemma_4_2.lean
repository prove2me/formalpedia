-- Prove2me | solution 1 for WrightPDIPM.Potential.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:38:13.054145+00:00
-- url     : https://prove2.me/submissions/5b6732c7-faf3-4778-83b9-4b822d416ec0

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
open Matrix
open WrightPDIPM.Potential

theorem g69b_phin_eq {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) :
    0 < mu x s ∧ Phi (n : ℝ) x s - (n : ℝ) * Real.log n =
      ∑ i, (x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hxs : 0 < x ⬝ᵥ s := by
    unfold dotProduct
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmu : 0 < mu x s := div_pos hxs hn'
  refine ⟨hmu, ?_⟩
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have e1 : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have e2 : ∑ i, x i * s i = x ⬝ᵥ s := rfl
  rw [e2, e1]
  simp_rw [Real.log_div (hw _).ne' hmu.ne']
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Phi
  rw [e1, Real.log_mul hn'.ne' hmu.ne']
  field_simp
  ring

theorem solution {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) :
    (n : ℝ) * Real.log n ≤ Phi (n : ℝ) x s ∧
      (Phi (n : ℝ) x s = (n : ℝ) * Real.log n ↔ ∀ i, x i * s i = mu x s) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Phi]
  obtain ⟨hmu, he⟩ := g69b_phin_eq hn x s hx hs
  have hd : ∀ i, 0 ≤ x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s) := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (mul_pos (hx i) (hs i)) hmu)
    linarith
  refine ⟨?_, ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hd i)
    linarith
  · constructor
    · intro h
      have h0 : ∑ i, (x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s)) = 0 := by
        linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd i)] at h0
      intro i
      have hi := h0 i (Finset.mem_univ i)
      have hp := div_pos (mul_pos (hx i) (hs i)) hmu
      by_contra hne
      have h1 : x i * s i / mu x s ≠ 1 := by
        intro h1; apply hne; field_simp at h1; linarith
      have := Real.log_lt_sub_one_of_pos hp h1
      linarith
    · intro h
      have h0 : ∑ i, (x i * s i / mu x s - 1 - Real.log (x i * s i / mu x s)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [h i, div_self hmu.ne']
        simp
      linarith
