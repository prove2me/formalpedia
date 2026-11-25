-- Prove2me | solution 1 for SZ.node_g2_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:19.592634+00:00
-- url     : https://prove2.me/submissions/0484ae56-ace5-44cc-a5e0-7fa6e62cf792

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {N : ℕ} (hno : ∀ i, ¬ Branching (node β (N + i)))
    {j k : ℕ} (hjk : j ≤ k) (h2 : (node β (N + j)).g2 = true) :
    (node β (N + k)).g2 = true := by
  induction k, hjk using Nat.le_induction with
  | base => exact h2
  | succ k hk ih =>
    have e : N + (k + 1) = (N + k) + 1 := by omega
    rw [e, node_succ, nodeNext, if_neg (hno k)]
    simp [ih]
end SZ
