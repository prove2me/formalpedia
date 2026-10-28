-- Prove2me | solution 1 for VdNSim.Sparse.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:59:55.14215+00:00
-- url     : https://prove2.me/submissions/1cf98de3-ba22-4125-af7d-70370b80b5df

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace Aux_VdN9
open VdNSim.Sparse

lemma entry_eq {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (x y : X) (j : Fin s)
    (hj : D.r j x = y) (hα : D.α j x ≠ 0) : A y x = D.α j x := by
  rw [D.eq2]
  apply Finset.sum_eq_single_of_mem j
  · simp [hj]
  · intro i hi hij
    have hri : D.r i x = y := (Finset.mem_filter.mp hi).2
    by_contra h
    exact hij (D.inj x i j h hα (by rw [hri, hj]))

end Aux_VdN9

open VdNSim.Sparse in
theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hsp : IsSparse s A)
    (D : ColumnData A s) (y : X) :
    ((Finset.univ.filter fun x =>
      ∃ j : Fin s, D.r j x = y ∧ D.α j x ≠ 0).card ≤ s) ∧
    (∀ i : Fin s,
      (Finset.univ.filter fun x => D.r i x = y ∧ D.α i x ≠ 0).card ≤ s) := by
  refine ⟨le_trans (Finset.card_le_card ?_) (hsp.2 y), fun i =>
    le_trans (Finset.card_le_card ?_) (hsp.2 y)⟩
  · intro x hx
    obtain ⟨j, hj, hα⟩ := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Aux_VdN9.entry_eq D x y j hj hα]
    exact hα
  · intro x hx
    obtain ⟨hj, hα⟩ := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Aux_VdN9.entry_eq D x y i hj hα]
    exact hα
