-- Prove2me | solution 1 for QuantumLTF.Membership.boundarySearchTree_depth
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T02:41:53.159442+00:00
-- url     : https://prove2.me/submissions/89f88dd4-4d36-4fde-9ed6-f0c5c5c9d639

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree

open QuantumLTF.Membership

private theorem map_depth {n : ℕ} {α β : Type} (g : α → β)
    (T : QueryTree n α) : (T.map g).depth = T.depth := by
  induction T with
  | leaf a => rfl
  | query x next ih =>
      simp only [QueryTree.map, QueryTree.depth]
      rw [ih 1, ih (-1)]

private theorem bisect_depth {n q : ℕ} (p : EuclideanSpace ℝ (Fin n))
    (s : ℤ) (lo hi : ℝ) : (boundaryBisect p s q lo hi).depth = q := by
  induction q generalizing lo hi with
  | zero => rfl
  | succ q ih =>
      simp only [boundaryBisect, QueryTree.depth]
      split <;> simp [ih, Nat.add_comm]

theorem solution {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) (L : ℝ) (q : ℕ) :
    (boundarySearchTree p L q).depth = q + 2 := by
  simp [boundarySearchTree, QueryTree.depth, map_depth, bisect_depth,
    Nat.add_comm, Nat.add_left_comm]
