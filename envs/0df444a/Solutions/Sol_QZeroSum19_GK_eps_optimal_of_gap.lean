-- Prove2me | solution 1 for QZeroSum19.GK.eps_optimal_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:24:31.222963+00:00
-- url     : https://prove2.me/submissions/fafa51fa-02cb-4788-9404-51f4135971b5

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

open QZeroSum19.GK in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hy : y ∈ stdSimplex ℝ (Fin m)) (h : ∀ i j, (A *ᵥ y) i - (Aᵀ *ᵥ x) j ≤ ε) :
    IsEpsOptimalAlice A ε x ∧ IsEpsOptimalBob A ε y := by
  have hn : Nonempty (Fin n) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have := hx.2
      simp at this
    · exact ⟨⟨0, h0⟩⟩
  have key : ∀ y' ∈ stdSimplex ℝ (Fin m), ∀ i, (A *ᵥ y) i - ε ≤ ⨆ i', (A *ᵥ y') i' := by
    intro y' hy' i
    have e : x ⬝ᵥ (A *ᵥ y') = (Aᵀ *ᵥ x) ⬝ᵥ y' := by
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have lower : (A *ᵥ y) i - ε ≤ (Aᵀ *ᵥ x) ⬝ᵥ y' := by
      have : ∑ j, ((A *ᵥ y) i - ε) * y' j ≤ ∑ j, (Aᵀ *ᵥ x) j * y' j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (hy'.1 j)
        linarith [h i j]
      rw [← Finset.mul_sum, hy'.2, mul_one] at this
      exact this
    have upper : x ⬝ᵥ (A *ᵥ y') ≤ ⨆ i', (A *ᵥ y') i' := by
      have : ∑ i', x i' * (A *ᵥ y') i' ≤ ∑ i', x i' * ⨆ i'', (A *ᵥ y') i'' := by
        apply Finset.sum_le_sum
        intro i' _
        exact mul_le_mul_of_nonneg_left (le_ciSup (Set.finite_range _).bddAbove i') (hx.1 i')
      rw [← Finset.sum_mul, hx.2, one_mul] at this
      exact this
    linarith
  have hne : ((fun y' => ⨆ i, (A *ᵥ y') i) '' stdSimplex ℝ (Fin m)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ hy⟩
  refine ⟨⟨hx, ?_⟩, ⟨hy, ?_⟩⟩
  · intro j
    have hbdd : BddBelow ((fun y' => ⨆ i, (A *ᵥ y') i) '' stdSimplex ℝ (Fin m)) := by
      refine ⟨(A *ᵥ y) (Classical.arbitrary (Fin n)) - ε, ?_⟩
      rintro b ⟨y', hy', rfl⟩
      exact key y' hy' _
    have h1 : gameValue A ≤ ⨆ i, (A *ᵥ y) i :=
      csInf_le hbdd (Set.mem_image_of_mem _ hy)
    have h2 : ⨆ i, (A *ᵥ y) i ≤ (Aᵀ *ᵥ x) j + ε := by
      apply ciSup_le
      intro i
      linarith [h i j]
    linarith
  · intro i
    have : (A *ᵥ y) i - ε ≤ gameValue A := by
      apply le_csInf hne
      rintro b ⟨y', hy', rfl⟩
      exact key y' hy' i
    linarith
