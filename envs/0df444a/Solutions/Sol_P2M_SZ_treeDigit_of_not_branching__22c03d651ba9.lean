-- Prove2me | solution 1 for P2M_SZ_treeDigit_of_not_branching__22c03d651ba9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:54:58.974499+00:00
-- url     : https://prove2.me/submissions/0d0ef708-36ad-40b1-9896-f364049cecd2

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_treeDigit_of_not_branching
import Theorems.Thm_SZ_node_st_of_not_branching

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) {N : ℕ}
    (hno : ∀ i, ¬ Branching (node β (N + i))) (j : ℕ) :
    treeDigit β (N + j) = gDigit (node β N).st j := by
  rw [treeDigit_of_not_branching β (hno j), node_st_of_not_branching β hno j, gDigit]
end SZ
