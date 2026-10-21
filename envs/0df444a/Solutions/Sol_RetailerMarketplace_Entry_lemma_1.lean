-- Prove2me | solution 1 for RetailerMarketplace.Entry.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:37:38.377996+00:00
-- url     : https://prove2.me/submissions/075c18fd-670f-4d03-a6ab-995cbc3e2e63

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

set_option autoImplicit false
open RetailerMarketplace.Entry

theorem rme_hD (f lam : ℝ) (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - f * (1 - lam) := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hl0, hl1⟩ := hlam
  nlinarith [mul_nonneg hf0 hl0]

theorem solution (c f lam v : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (0 ≤ piSBT_T c f v ↔ vT c f ≤ v) ∧
      (0 < lam → lam < 1 → (0 ≤ piSBMT_T c f lam v ↔ vT c f ≤ v)) ∧
      pbarT c f lam (vT c f) = vT c f ∧
      (v ∈ mp c f ↔ vT c f ≤ v) := by
  have h1 : 0 < 1 - f := by linarith [hf.2]
  have hD := rme_hD f lam hf hlam
  have key : vT c f ≤ v ↔ c ≤ v * (1 - f) := by
    unfold vT; rw [div_le_iff₀ h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold piSBT_T; rw [key]; constructor <;> intro h <;> nlinarith
  · intro hl0 hl1
    have e : piSBMT_T c f lam v = (1 - lam) * lam / (1 - f * (1 - lam)) * ((1 - f) * v - c) := by
      have hD0 := hD.ne'
      unfold piSBMT_T pbarT
      generalize hDd : 1 - f * (1 - lam) = D at hD0 ⊢
      field_simp
      subst hDd
      ring
    rw [e, key]
    have hp : 0 < (1 - lam) * lam / (1 - f * (1 - lam)) := by
      apply div_pos (mul_pos (by linarith) hl0) hD
    constructor
    · intro h
      have := nonneg_of_mul_nonneg_right h hp
      nlinarith
    · intro h
      apply mul_nonneg hp.le
      nlinarith
  · have hD0 := hD.ne'
    have h1' := h1.ne'
    unfold pbarT vT
    generalize hDd : 1 - f * (1 - lam) = D at hD0 ⊢
    generalize hEd : 1 - f = E at h1' ⊢
    field_simp
    subst hDd
    subst hEd
    ring
  · unfold mp
    simp only [Set.mem_setOf_eq]
    exact key.symm
