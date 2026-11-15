-- Prove2me | solution 1 for QuantumLTF.Membership.boundarySearchTreeStrict_depth
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:30:42.996959+00:00
-- url     : https://prove2.me/submissions/d32a5e1e-f5da-44a4-9936-264662ec312b

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict

open QuantumLTF.Membership

private theorem map_depth_strict {n : ℕ} {α β : Type} (g : α → β)
    (T : QueryTree n α) : (T.map g).depth = T.depth := by
  induction T with
  | leaf a => rfl
  | query x next ih =>
      simp only [QueryTree.map, QueryTree.depth]
      rw [ih 1, ih (-1)]

private theorem bisect_depth_strict {n q : ℕ} (p : EuclideanSpace ℝ (Fin n))
    (s : ℤ) (lo hi : ℝ) : (boundaryBisect p s q lo hi).depth = q := by
  induction q generalizing lo hi with
  | zero => rfl
  | succ q ih =>
      simp only [boundaryBisect, QueryTree.depth]
      split <;> simp [ih, Nat.add_comm]

theorem solution {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) (L : ℝ) (q : ℕ) :
    (boundarySearchTreeStrict p L q).depth = q + 2 := by
  simp [boundarySearchTreeStrict, QueryTree.depth, map_depth_strict,
    bisect_depth_strict, Nat.add_comm, Nat.add_left_comm]
