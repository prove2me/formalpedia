-- Prove2me | solution 1 for PairwiseRealize.sec_A_2_total_trade
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:48:32.057888+00:00
-- url     : https://prove2.me/submissions/fb97c875-1a7a-489a-8f8a-6c48fe5ce8ad

import Mathlib
import Definitions.Def_PairwiseRealize_Model

open PairwiseRealize in
theorem solution (n : ℕ) (hn : 2 ≤ n) (τ : Row n) :
    let i₁ : Fin n := ⟨0, by omega⟩
    let i₂ : Fin n := ⟨1, by omega⟩
    let flip : Row n → Fin n → Row n := fun x i => Function.update x i (!x i)
    let Δ : Feat n → ℤ := fun f =>
      wvec n (flip τ i₁) f + wvec n (flip τ i₂) f - wvec n (flip (flip τ i₁) i₂) f
    Δ Feat.total = 1 ∧ (∀ i, Δ (Feat.single i) = bv (τ i)) ∧
      ∀ i j (h : i < j), |Δ (Feat.pair i j h)| ≤ 1 := by
  intro i₁ i₂ flip Δ
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have hflip : ∀ (x : Row n) (k m : Fin n), flip x k m = if m = k then !x k else x m := by
    intro x k m
    simp only [flip, Function.update_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp [Δ, wvec]
  · intro i
    simp only [Δ, wvec, hflip]
    by_cases h1 : i = i₁
    · rw [h1]
      simp only [if_true, if_neg h12]
      cases τ i₁ <;> simp [bv, h12, h12.symm]
    · by_cases h2 : i = i₂
      · rw [h2]
        simp only [if_true, if_neg h1]
        cases τ i₂ <;> simp [bv, h12, h12.symm]
      · simp only [if_neg h1, if_neg h2]
        ring
  · intro i j h
    simp only [Δ, wvec, hflip]
    have hij : i ≠ j := ne_of_lt h
    have hj1 : j ≠ i₁ := by
      intro hj; rw [hj] at h; exact absurd h (by simp [i₁, Fin.lt_iff_val_lt_val])
    by_cases hi1 : i = i₁
    · rw [hi1]
      by_cases hj2 : j = i₂
      · rw [hj2]
        simp only [if_true, if_neg h12, if_neg h12.symm]
        cases τ i₁ <;> cases τ i₂ <;> simp [bv, h12, h12.symm]
      · simp only [if_true, if_neg h12, if_neg hj1, if_neg hj2]
        cases τ i₁ <;> cases τ j <;> simp [bv, h12, h12.symm]
    · by_cases hi2 : i = i₂
      · rw [hi2]
        simp only [if_true, if_neg hi1, if_neg hj1]
        by_cases hj2 : j = i₂
        · exact absurd (hi2.trans hj2.symm) hij
        · simp only [if_neg hj2]
          cases τ i₂ <;> cases τ j <;> simp [bv, h12, h12.symm]
      · by_cases hj2 : j = i₂
        · simp only [if_neg hi1, if_neg hi2, if_neg hj1, hj2, if_true, if_neg h12.symm]
          cases τ i <;> cases τ i₂ <;> simp [bv, h12, h12.symm]
        · simp only [if_neg hi1, if_neg hi2, if_neg hj1, if_neg hj2]
          cases τ i <;> cases τ j <;> simp [bv, h12, h12.symm]
