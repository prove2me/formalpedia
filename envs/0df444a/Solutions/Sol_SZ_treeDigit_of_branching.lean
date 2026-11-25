-- Prove2me | solution 1 for SZ.treeDigit_of_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:25.962725+00:00
-- url     : https://prove2.me/submissions/eab84b5a-ace3-4d72-93b5-b9e8e432fe80

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {k : ℕ} (h : Branching (node β k)) :
    treeDigit β k = branchDigit (valS (node β k).st) (β (node β k).used) := by
  rw [treeDigit, nodeDigit, if_pos h]
end SZ
