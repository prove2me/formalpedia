-- Prove2me | solution 1 for SZ.node_used_succ_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:47.066223+00:00
-- url     : https://prove2.me/submissions/d3560798-01a3-4709-a190-617444a05504

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    (node β (k + 1)).used = (node β k).used := by
  rw [node_succ, nodeNext, if_neg h]
end SZ
