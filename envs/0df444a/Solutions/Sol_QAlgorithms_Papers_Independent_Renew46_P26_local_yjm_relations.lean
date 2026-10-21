-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.local_yjm_relations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:36:15.7419+00:00
-- url     : https://prove2.me/submissions/23428ff2-56f8-4249-9258-a59421f0c2e2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem g64f_single_mul_swap {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n) :
    s * Equiv.swap a b = Equiv.swap (s a) (s b) * s := by
  rw [Equiv.swap_apply_apply]; group

theorem g64f_yjm_eq {n : ℕ} (j : Fin n) :
    yjm j = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j),
      MonoidAlgebra.single (Equiv.swap k j) (1 : ℂ) := rfl

theorem solution {n : ℕ} (i : Adjacent n) :
    (∀ j : Fin n, j ≠ i.val → j ≠ nextPosition i →
      adjacentElement i * yjm j = yjm j * adjacentElement i) ∧
    adjacentElement i * yjm i.val + 1 = yjm (nextPosition i) * adjacentElement i := by
  set s := adjacentPerm i with hs
  have hsi : s i.val = nextPosition i := by simp [hs, adjacentPerm]
  have hsn : s (nextPosition i) = i.val := by simp [hs, adjacentPerm]
  have hss : s * s = 1 := by simp [hs, adjacentPerm, Equiv.swap_mul_self]
  have hlt : i.val < nextPosition i := by
    rw [Fin.lt_def]; simp [nextPosition]
  have hadj : ∀ k : Fin n, k < nextPosition i → k ≠ i.val → k < i.val := by
    intro k hk hne
    rw [Fin.lt_def] at hk ⊢
    simp [nextPosition] at hk
    have : k.val ≠ i.val.val := fun h => hne (Fin.ext h)
    omega
  constructor
  · intro j hj1 hj2
    have hsj : s j = j := by
      simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne hj1 hj2
    simp only [adjacentElement, g64f_yjm_eq, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, one_mul]
    refine Finset.sum_nbij' (fun k => s k) (fun k => s k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_cases h1 : k = i.val
      · subst h1; rw [hsi]
        rcases lt_or_gt_of_ne hj2 with h | h
        · exact absurd (hadj j h hj1) (by intro h'; exact absurd (lt_trans h' hk) (lt_irrefl _))
        · exact h
      by_cases h2 : k = nextPosition i
      · subst h2; rw [hsn]; exact lt_trans hlt hk
      · have : s k = k := by
          simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [this]; exact hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_cases h1 : k = i.val
      · subst h1; rw [hsi]
        rcases lt_or_gt_of_ne hj2 with h | h
        · exact absurd (hadj j h hj1) (by intro h'; exact absurd (lt_trans h' hk) (lt_irrefl _))
        · exact h
      by_cases h2 : k = nextPosition i
      · subst h2; rw [hsn]; exact lt_trans hlt hk
      · have : s k = k := by
          simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [this]; exact hk
    · intro k _; rw [← Equiv.Perm.mul_apply, hss, Equiv.Perm.one_apply]
    · intro k _; rw [← Equiv.Perm.mul_apply, hss, Equiv.Perm.one_apply]
    · intro k _
      rw [g64f_single_mul_swap, hsj]
  · have hset : Finset.univ.filter (fun k : Fin n => k < nextPosition i) =
        insert i.val (Finset.univ.filter (fun k : Fin n => k < i.val)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hk; by_cases h : k = i.val
        · exact Or.inl h
        · exact Or.inr (hadj k hk h)
      · rintro (h | h)
        · rw [h]; exact hlt
        · exact lt_trans h hlt
    simp only [adjacentElement, g64f_yjm_eq, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, one_mul]
    rw [hset, Finset.sum_insert (by simp), add_comm]
    congr 1
    · rw [show Equiv.swap i.val (nextPosition i) = s from rfl, hss]; rfl
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [g64f_single_mul_swap]
      have hk1 : k ≠ i.val := ne_of_lt hk
      have hk2 : k ≠ nextPosition i := ne_of_lt (lt_trans hk hlt)
      have : s k = k := by
        simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne hk1 hk2
      rw [this, hsi]
