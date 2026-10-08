-- Prove2me | solution 1 for SchedComplexity.Tardiness.idle_time_removal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:10:50.138977+00:00
-- url     : https://prove2.me/submissions/bef20a09-8038-4882-a4b8-b82e16eddc1d

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Model



namespace SchedComplexity.Tardiness

lemma tard_posCompletion_succ {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    posCompletion p π (i.val + 1) = posCompletion p π i.val + p (π i) := by
  unfold posCompletion
  have : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j; simp [Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]; ring

lemma tard_posCompletion_mono {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) {k l : ℕ}
    (h : k ≤ l) : posCompletion p π k ≤ posCompletion p π l := by
  unfold posCompletion
  apply Finset.sum_le_sum_of_subset
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

lemma tard_posCompletion_zero {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    posCompletion p π 0 = 0 := by
  unfold posCompletion; simp

lemma tard_noIdle_feasible {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    IsFeasible p (noIdleStart p π) := by
  intro i j hij
  have key : ∀ i j : Fin n, (π.symm i).val < (π.symm j).val →
      noIdleStart p π i + p i ≤ noIdleStart p π j := by
    intro i j h
    unfold noIdleStart
    have := tard_posCompletion_succ p π (π.symm i)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]
    exact tard_posCompletion_mono p π (by omega)
  have : (π.symm i).val ≠ (π.symm j).val := by
    intro h; apply hij; have := Fin.ext h; simpa using this
  rcases lt_or_gt_of_ne this with h | h
  · exact Or.inl (key i j h)
  · exact Or.inr (key j i h)

theorem idle_time_removal_core {n : ℕ} (p w d : Fin n → ℕ) :
    (∀ π : Equiv.Perm (Fin n), IsFeasible p (noIdleStart p π)) ∧
    ∀ S : Fin n → ℕ, IsFeasible p S →
      ∃ π : Equiv.Perm (Fin n), orderTWT p w d π ≤ totalWeightedTardiness p w d S := by
  refine ⟨tard_noIdle_feasible p, ?_⟩
  intro S hS
  let key : Fin n → ℕ ×ₗ ℕ := fun j => toLex (S j, p j)
  refine ⟨Tuple.sort key, ?_⟩
  set π := Tuple.sort key with hπ
  have hmono : Monotone (key ∘ π) := Tuple.monotone_sort key
  have step : ∀ k : ℕ, (hk : k < n) → posCompletion p π k ≤ S (π ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; rw [tard_posCompletion_zero]; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := tard_posCompletion_succ p π ⟨k, by omega⟩
      simp only at h2
      rw [h2]
      have hle : key (π ⟨k, by omega⟩) ≤ key (π ⟨k+1, hk⟩) :=
        hmono (show (⟨k, by omega⟩ : Fin n) ≤ ⟨k+1, hk⟩ from by simp [Fin.le_def])
      have hne : π ⟨k, by omega⟩ ≠ π ⟨k+1, hk⟩ := by
        intro h; have := π.injective h; simp [Fin.ext_iff] at this
      have hf := hS _ _ hne
      simp only [key, Function.comp, Prod.Lex.le_iff, ofLex_toLex] at hle
      omega
  unfold orderTWT totalWeightedTardiness
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold tardiness completion
  apply max_le_max le_rfl
  have := step (π.symm j).val (π.symm j).isLt
  simp only [Fin.eta, Equiv.apply_symm_apply] at this
  unfold noIdleStart
  have : posCompletion p π (π.symm j).val ≤ S j := this
  omega

end SchedComplexity.Tardiness

open SchedComplexity.Tardiness


theorem solution {n : ℕ} (p w d : Fin n → ℕ) :
    (∀ π : Equiv.Perm (Fin n), IsFeasible p (noIdleStart p π)) ∧
    ∀ S : Fin n → ℕ, IsFeasible p S →
      ∃ π : Equiv.Perm (Fin n), orderTWT p w d π ≤ totalWeightedTardiness p w d S := by
  exact idle_time_removal_core p w d
