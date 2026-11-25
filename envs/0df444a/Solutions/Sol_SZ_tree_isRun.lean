-- Prove2me | solution 1 for SZ.tree_isRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:03.064511+00:00
-- url     : https://prove2.me/submissions/05bd31cc-ed6c-4c73-bea7-6914dd504149

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_node_st_eq_runState
import Theorems.Thm_SZ_nodeDigit_adm
import Theorems.Thm_SZ_tree_val_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) : IsRun (-12, 9) (treeDigit β) := by
  intro k
  rw [← node_st_eq_runState]
  exact nodeDigit_adm β (node β k) (tree_val_mem β k).1 (tree_val_mem β k).2
end SZ
