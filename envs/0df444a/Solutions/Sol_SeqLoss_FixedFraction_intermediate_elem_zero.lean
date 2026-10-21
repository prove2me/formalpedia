-- Prove2me | solution 1 for SeqLoss.FixedFraction.intermediate_elem_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:11:14.882202+00:00
-- url     : https://prove2.me/submissions/1290c45c-6744-4e18-8066-704d08121d2e

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_FixedFraction_Axioms

set_option autoImplicit false
open SeqLoss.FixedFraction

theorem slf_isLoss_elem (n : ℕ) : IsLoss (elem n) := by
  intro i; unfold elem; split_ifs <;> norm_num

theorem slf_sum_elem (n : ℕ) (hn : 1 ≤ n) : ∑ i, elem n i = 1 := by
  rw [Finset.sum_eq_single ⟨n - 1, by omega⟩]
  · simp [elem]; omega
  · intro j _ hj
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    unfold elem
    rw [if_neg (by omega)]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slf_phi2_e3 (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hmp : MergingProof φ) : φ 3 (elem 3) 1 = 0 := by
  obtain ⟨h1, h2⟩ := hmp
  have e3 := (hφ 3 (elem 3) (slf_isLoss_elem 3)).1
  have e2 := (hφ 2 (elem 2) (slf_isLoss_elem 2)).1
  obtain ⟨nn3, -, t3⟩ := e3
  obtain ⟨nn2, -, t2⟩ := e2
  rw [slf_sum_elem 3 (by norm_num), Fin.sum_univ_three] at t3
  rw [slf_sum_elem 2 (by norm_num), Fin.sum_univ_two] at t2
  have a0 := nn3 0
  have a1 := nn3 1
  have a2 := nn3 2
  exact le_antisymm (by linarith) a1

/-- first-component of `e_m` is non-increasing in m (for m ≥ 3 index 1 goes down) -/
theorem slf_B (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ m : ℕ, 3 ≤ m → ∀ i : Fin m, i.val = 1 → φ m (elem m) i ≤ 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro i hi
    have : i = 1 := Fin.ext (by simpa using hi)
    subst this
    exact (slf_phi2_e3 φ hφ hmp).le
  | succ m hm ih =>
    intro i hi
    have h := (hpm m 2 (by norm_num) (by omega) ⟨1, by omega⟩ ⟨m - 1, by omega⟩ (by simp) (by simp; omega)).1
    have hi' : i = (⟨1, by omega⟩ : Fin m).castSucc := Fin.ext (by simpa using hi)
    rw [hi']
    exact h.trans (ih ⟨1, by omega⟩ rfl)

theorem slf_C (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hpm : PopulationMonotone φ)
    (n : ℕ) (k : Fin n) (hk : 1 ≤ k.val) :
    φ (n + 1) (elem (n + 1)) k.succ ≤ φ n (elem n) k := by
  have hn : 1 < n := by have := k.isLt; omega
  exact (hpm n 1 le_rfl hn ⟨0, by omega⟩ k (by simp) (by omega)).2

theorem slf_inter (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) :
    ∀ (n : ℕ) (i : Fin n), 1 ≤ i.val → i.val + 1 < n → φ n (elem n) i = 0 := by
  have S : ∀ c n : ℕ, ∀ i : Fin (n + 1), i.val = c + 1 → i.val + 1 < n + 1 →
      φ (n + 1) (elem (n + 1)) i ≤ 0 := by
    intro c
    induction c with
    | zero =>
      intro n i hi hin
      exact slf_B φ hφ hpm hmp (n + 1) (by omega) i hi
    | succ c ih =>
      intro n i hi hin
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hk : c + 1 < n' + 1 := by omega
      have hi' : i = (⟨c + 1, hk⟩ : Fin (n' + 1)).succ := Fin.ext (by simpa using hi)
      rw [hi']
      refine (slf_C φ hpm (n' + 1) ⟨c + 1, hk⟩ (by simp)).trans ?_
      exact ih n' ⟨c + 1, hk⟩ rfl (by simp; omega)
  intro n i h1 h2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, i.val = c + 1 := ⟨i.val - 1, by omega⟩
  exact le_antisymm (S c n' i hc h2) ((hφ _ (elem _) (slf_isLoss_elem _)).1.1 i)
theorem solution (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) (hφ : IsRule φ)
    (hpm : PopulationMonotone φ) (hmp : MergingProof φ) (n : ℕ) (i : Fin n)
    (hi1 : 1 ≤ i.val) (hin : i.val + 1 < n) :
    φ n (elem n) i = 0 := slf_inter φ hφ hpm hmp n i hi1 hin
