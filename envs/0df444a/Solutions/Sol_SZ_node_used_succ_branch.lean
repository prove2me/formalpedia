-- Prove2me | solution 1 for SZ.node_used_succ_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:00:25.165613+00:00
-- url     : https://prove2.me/submissions/cae37283-4d8b-44b2-bbcb-759aede18bbc

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used + 1 := by
  rw [node_succ, nodeNext, if_pos h]
end SZ
