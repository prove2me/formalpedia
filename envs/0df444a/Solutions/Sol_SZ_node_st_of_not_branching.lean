-- Prove2me | solution 1 for SZ.node_st_of_not_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:23.737838+00:00
-- url     : https://prove2.me/submissions/3c2c637b-5366-4a77-8f74-9b5ebd2a1f60

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gState_succ
import Theorems.Thm_SZ_node_st_succ
import Theorems.Thm_SZ_treeDigit_of_not_branching

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    (node β (N + j)).st = gState (node β N).st j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e : N + (j + 1) = (N + j) + 1 := by omega
    rw [e, node_st_succ, treeDigit_of_not_branching β (hno j), ih, gState_succ]
    rfl
end SZ
