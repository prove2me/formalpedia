-- Prove2me | solution 1 for SZ.node_st_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:31:05.552931+00:00
-- url     : https://prove2.me/submissions/aea45238-b646-4b3b-81b0-b36b65691a5f

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (k : ℕ) :
    (node β (k + 1)).st = stepS (node β k).st (treeDigit β k) := by
  rw [node_succ, nodeNext, treeDigit]
  split_ifs <;> rfl
end SZ
