-- Prove2me | solution 1 for SZ.treeXi_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:34.722955+00:00
-- url     : https://prove2.me/submissions/e9c7b8de-dd68-49b9-b126-1c8fb7d76c84

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_tree_isRun
import Theorems.Thm_SZ_runXi_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) : 4 / 3 ≤ treeXi β ∧ treeXi β ≤ 5 / 3 :=
  runXi_mem (tree_isRun β)
end SZ
