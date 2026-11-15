-- Prove2me | solution 1 for QuantumLTF.Membership.QueryTree_run_map
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T02:44:33.1666+00:00
-- url     : https://prove2.me/submissions/6683752e-0de4-4c33-9731-4b3401335a2a

import Mathlib
import Definitions.Def_QuantumLTF_Membership_boundarySearchTree

open QuantumLTF.Membership

theorem solution {n : ℕ} {α β : Type} (g : α → β)
    (T : QueryTree n α) (f : EuclideanSpace ℝ (Fin n) → ℤ) :
    (T.map g).run f = g (T.run f) := by
  induction T with
  | leaf a => rfl
  | query x next ih =>
      simp only [QueryTree.map, QueryTree.run]
      exact ih (f x)
