-- Prove2me | solution 1 for ProphetBipartite.eq_14_ge_third_opt
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:35:04.792244+00:00
-- url     : https://prove2.me/submissions/1335e140-9979-40e4-a50a-c3a439f93854

import Mathlib
import Definitions.Def_ProphetBipartite_IsSolution17

open ProphetBipartite in
theorem solution {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (M Q : L → R → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) (hlr : IsSolution17 M Q l r) :
    (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ r j) ∧
      ∀ (SL : Finset L) (SR : Finset R),
        ∑ i, ∑ j, M i j ≤
          3 * (∑ i ∈ SL, l i + ∑ j ∈ SR, r j +
            ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, max (M i j - (l i + r j) * Q i j) 0) := by
  have hl0 : ∀ i, 0 ≤ l i := by
    intro i
    rw [hlr.1 i]
    exact Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hr0 : ∀ j, 0 ≤ r j := by
    intro j
    rw [hlr.2 j]
    exact Finset.sum_nonneg (fun i _ => le_max_right _ _)
  refine ⟨hl0, hr0, ?_⟩
  intro SL SR
  obtain ⟨A, hAdef⟩ : ∃ A : L → R → ℝ, A = fun i j => max (M i j - Q i j * (l i + r j)) 0 :=
    ⟨_, rfl⟩
  have hAij : ∀ i j, A i j = max (M i j - Q i j * (l i + r j)) 0 := by
    intro i j
    rw [hAdef]
  have hA0 : ∀ i j, 0 ≤ A i j := by
    intro i j
    rw [hAij]
    exact le_max_right _ _
  have hl' : ∀ i, l i = ∑ j, A i j := fun i =>
    (hlr.1 i).trans (Finset.sum_congr rfl (fun j _ => (hAij i j).symm))
  have hr' : ∀ j, r j = ∑ i, A i j := fun j =>
    (hlr.2 j).trans (Finset.sum_congr rfl (fun i _ => (hAij i j).symm))
  have hMA : ∀ i j, M i j ≤ A i j + Q i j * l i + Q i j * r j := by
    intro i j
    rw [hAij]
    have h1 := le_max_left (M i j - Q i j * (l i + r j)) 0
    have e : Q i j * (l i + r j) = Q i j * l i + Q i j * r j := by ring
    linarith
  have h1 : ∑ i, ∑ j, M i j ≤ ∑ i, ∑ j, (A i j + Q i j * l i + Q i j * r j) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hMA i j))
  have hsplit : ∑ i, ∑ j, (A i j + Q i j * l i + Q i j * r j) =
      ∑ i, ∑ j, A i j + ∑ i, ∑ j, Q i j * l i + ∑ i, ∑ j, Q i j * r j := by
    simp only [Finset.sum_add_distrib]
  have hQl : ∑ i, ∑ j, Q i j * l i ≤ ∑ i, l i :=
    Finset.sum_le_sum (fun i _ => by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (hl0 i) (hrow i))
  have hQr : ∑ i, ∑ j, Q i j * r j ≤ ∑ j, r j := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (hr0 j) (hcol j))
  have hsl : ∑ i, l i = ∑ i, ∑ j, A i j := Finset.sum_congr rfl (fun i _ => hl' i)
  have hsr : ∑ j, r j = ∑ i, ∑ j, A i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hr' j)
  have e1 : ∑ i, ∑ j, A i j = ∑ i ∈ SL, ∑ j, A i j + ∑ i ∈ SLᶜ, ∑ j, A i j :=
    (Finset.sum_add_sum_compl SL (fun i => ∑ j, A i j)).symm
  have e2 : ∑ i ∈ SLᶜ, ∑ j, A i j =
      ∑ i ∈ SLᶜ, ∑ j ∈ SR, A i j + ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, A i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Finset.sum_add_sum_compl SR (fun j => A i j)).symm)
  have e3 : ∑ i ∈ SL, ∑ j, A i j = ∑ i ∈ SL, l i :=
    Finset.sum_congr rfl (fun i _ => (hl' i).symm)
  have e4 : ∑ i ∈ SLᶜ, ∑ j ∈ SR, A i j ≤ ∑ j ∈ SR, r j := by
    calc ∑ i ∈ SLᶜ, ∑ j ∈ SR, A i j ≤ ∑ i, ∑ j ∈ SR, A i j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => Finset.sum_nonneg (fun j _ => hA0 i j))
      _ = ∑ j ∈ SR, ∑ i, A i j := Finset.sum_comm
      _ = ∑ j ∈ SR, r j := Finset.sum_congr rfl (fun j _ => (hr' j).symm)
  have hbr : ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, max (M i j - (l i + r j) * Q i j) 0 =
      ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, A i j :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [hAij, mul_comm (l i + r j) (Q i j)]))
  rw [hbr]
  linarith
