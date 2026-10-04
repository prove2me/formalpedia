-- Prove2me | solution 1 for SennottDP.Fatou.liminf_finite_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:31:00.058148+00:00
-- url     : https://prove2.me/submissions/ba1d9c73-7657-4e38-a6ca-3d89ebb84b45

import Mathlib

open Filter Topology
open scoped ENNReal

open Filter Topology in
theorem dd8dd4c4_aux {G : Type*} (s : Finset G) (u : G → ℕ → EReal) :
    ∑ j ∈ s, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑ j ∈ s, u j N) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [liminf_const]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc liminf (fun N => u a N) atTop + ∑ j ∈ s, liminf (fun N => u j N) atTop
        ≤ liminf (fun N => u a N) atTop + liminf (fun N => ∑ j ∈ s, u j N) atTop :=
          add_le_add le_rfl ih
      _ ≤ liminf ((fun N => u a N) + (fun N => ∑ j ∈ s, u j N)) atTop := EReal.le_liminf_add
      _ = liminf (fun N => ∑ j ∈ insert a s, u j N) atTop := by
          congr 1
          funext N
          simp [Finset.sum_insert ha]

open Filter Topology in
theorem solution {G : Type*} [Fintype G] [Nonempty G] (u : G → ℕ → EReal)
    (hu : ∀ j N, u j N ≠ ⊥)
    (hind : ¬ ((∃ j, liminf (fun N => u j N) atTop = ⊥) ∧
      (∃ k, liminf (fun N => u k N) atTop = ⊤))) :
    ∑ j, liminf (fun N => u j N) atTop ≤ liminf (fun N => ∑ j, u j N) atTop := by
  exact dd8dd4c4_aux Finset.univ u
