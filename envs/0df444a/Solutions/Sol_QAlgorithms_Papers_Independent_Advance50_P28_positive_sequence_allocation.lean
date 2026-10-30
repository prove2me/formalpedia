-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P28.positive_sequence_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:52:40.575037+00:00
-- url     : https://prove2.me/submissions/632fff8b-bf9b-4449-8c73-0142a29ae7b5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open QAlgorithms.Papers.Independent.Advance50.P28
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {M N : ℕ} (hN : 0 < N) (hMN : N ≤ M)
    (alpha : Fin N → ℝ) (beta : Fin M → ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ j, 0 < beta j)
    (hmass : (∑ j, beta j) ≤ ∑ i, alpha i) :
    ∃ f : Fin M → Fin N,
      (∑ i, max ((∑ j, if f j = i then beta j else 0) - alpha i) 0) ≤
        (N : ℝ) * peak beta := by
  have hbp : ∀ j, beta j ≤ peak beta := fun j =>
    le_csSup (Set.finite_range beta).bddAbove ⟨j, rfl⟩
  have hM : 0 < M := lt_of_lt_of_le hN hMN
  have hpk : 0 ≤ peak beta := le_trans (hb ⟨0, hM⟩).le (hbp ⟨0, hM⟩)
  set load : ℕ → (Fin M → Fin N) → Fin N → ℝ :=
    fun k f i => ∑ j : Fin M, if j.val < k ∧ f j = i then beta j else 0 with hload
  have key : ∀ k : ℕ, k ≤ M → ∃ f : Fin M → Fin N, ∀ i, load k f i ≤ alpha i + peak beta := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hN⟩, fun i => ?_⟩
      simp only [hload]
      simp
      exact le_trans (le_refl _) (by linarith [ha i, hpk])
    | succ k ih =>
      intro hk
      obtain ⟨f, hf⟩ := ih (by omega)
      have hkM : k < M := by omega
      -- some bin has load < alpha
      have hex : ∃ i, load k f i < alpha i := by
        by_contra hcon
        push Not at hcon
        have h1 : ∑ i, alpha i ≤ ∑ i, load k f i := Finset.sum_le_sum (fun i _ => hcon i)
        have h2 : ∑ i, load k f i = ∑ j : Fin M, if j.val < k then beta j else 0 := by
          simp only [hload]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j.val < k
          · simp [hj]
          · simp [hj]
        have h3 : ∑ j : Fin M, (if j.val < k then beta j else 0) + beta ⟨k, hkM⟩ ≤ ∑ j, beta j := by
          have e : ∑ j : Fin M, (if j = (⟨k, hkM⟩ : Fin M) then beta j else 0) = beta ⟨k, hkM⟩ := by
            simp
          rw [← e, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j = (⟨k, hkM⟩ : Fin M)
          · subst hj
            simp
          · by_cases hj2 : j.val < k
            · simp [hj, hj2]
            · simp [hj, hj2, (hb j).le]
        linarith [hb ⟨k, hkM⟩]
      obtain ⟨i0, hi0⟩ := hex
      refine ⟨Function.update f ⟨k, hkM⟩ i0, fun i => ?_⟩
      have hstep : load (k + 1) (Function.update f ⟨k, hkM⟩ i0) i =
          load k f i + (if i0 = i then beta ⟨k, hkM⟩ else 0) := by
        simp only [hload]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hkM⟩ : Fin M))]
        conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨k, hkM⟩ : Fin M))]
        have e1 : ∑ j ∈ Finset.univ.erase (⟨k, hkM⟩ : Fin M),
            (if j.val < k + 1 ∧ Function.update f ⟨k, hkM⟩ i0 j = i then beta j else 0) =
            ∑ j ∈ Finset.univ.erase (⟨k, hkM⟩ : Fin M),
            (if j.val < k ∧ f j = i then beta j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hne : j ≠ ⟨k, hkM⟩ := Finset.ne_of_mem_erase hj
          have hjk : j.val ≠ k := fun h => hne (Fin.ext h)
          rw [Function.update_of_ne hne]
          have : j.val < k + 1 ↔ j.val < k := by omega
          simp only [this]
        rw [e1]
        simp
      rw [hstep]
      by_cases hi : i0 = i
      · subst hi
        rw [if_pos rfl]
        linarith [hbp ⟨k, hkM⟩]
      · rw [if_neg hi, add_zero]
        exact hf i
  obtain ⟨f, hf⟩ := key M le_rfl
  refine ⟨f, ?_⟩
  have : ∀ i, max ((∑ j, if f j = i then beta j else 0) - alpha i) 0 ≤ peak beta := by
    intro i
    apply max_le
    · have := hf i
      have e : load M f i = ∑ j, if f j = i then beta j else 0 := by
        simp only [hload]
        apply Finset.sum_congr rfl
        intro j _
        simp [j.2]
      linarith
    · exact hpk
  calc _ ≤ ∑ _i : Fin N, peak beta := Finset.sum_le_sum (fun i _ => this i)
    _ = _ := by simp
