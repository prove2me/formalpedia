-- Prove2me | solution 1 for SZ.treeDigit_of_not_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:18:59.972448+00:00
-- url     : https://prove2.me/submissions/d4c01932-0279-47bf-b538-1b50cfc89634

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {k : ℕ} (h : ¬ Branching (node β k)) :
    treeDigit β k = pick (valS (node β k).st) := by
  rw [treeDigit, nodeDigit, if_neg h]
end SZ
