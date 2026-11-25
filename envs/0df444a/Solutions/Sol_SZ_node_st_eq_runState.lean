-- Prove2me | solution 1 for SZ.node_st_eq_runState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:29.177606+00:00
-- url     : https://prove2.me/submissions/74389199-915b-4cbc-a382-05baa19ab49c

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runState_succ
import Theorems.Thm_SZ_node_st_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (k : ℕ) :
    (node β k).st = runState (-12, 9) (treeDigit β) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [node_st_succ, runState_succ, ih]
end SZ
