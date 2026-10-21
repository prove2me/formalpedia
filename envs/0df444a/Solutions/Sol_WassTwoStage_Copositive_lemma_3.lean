-- Prove2me | solution 1 for WassTwoStage.Copositive.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:29:39.718647+00:00
-- url     : https://prove2.me/submissions/c3b802d2-72ee-4799-beb5-87f48c3a102b

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

set_option autoImplicit false
open Matrix WassTwoStage.Copositive

theorem solution {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hCR : d.CompleteRecourse) :
    StrictlyCopositive (d.W * d.Wᵀ) := by
  intro v hv hv0
  obtain ⟨y, hy⟩ := hCR
  have h1 : v ⬝ᵥ ((d.W * d.Wᵀ) *ᵥ v) = (d.Wᵀ *ᵥ v) ⬝ᵥ (d.Wᵀ *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [h1]
  have hnn : 0 ≤ (d.Wᵀ *ᵥ v) ⬝ᵥ (d.Wᵀ *ᵥ v) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases hnn.eq_or_lt with h | h
  · exfalso
    have hz : d.Wᵀ *ᵥ v = 0 := dotProduct_self_eq_zero.1 h.symm
    have h2 : v ⬝ᵥ (d.W *ᵥ y) = 0 := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hz]; simp
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hv0 (funext hcon)
    have hpos : 0 < v i := lt_of_le_of_ne (hv i) (Ne.symm hi)
    have : 0 < v ⬝ᵥ (d.W *ᵥ y) := by
      unfold dotProduct
      apply Finset.sum_pos'
      · intro j _; exact mul_nonneg (hv j) (hy j).le
      · exact ⟨i, Finset.mem_univ _, mul_pos hpos (hy i)⟩
    linarith
  · exact h
