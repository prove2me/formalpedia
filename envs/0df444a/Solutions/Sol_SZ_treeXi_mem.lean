-- Prove2me | solution 1 for SZ.treeXi_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:22:12.350852+00:00
-- url     : https://prove2.me/submissions/2dbb19f8-dec7-4bcd-8809-62488c977d57

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_tree_isRun
import Theorems.Thm_SZ_tree_exists_fst_eq_zero
import Theorems.Thm_SZ_tree_exists_snd_eq_two
import Theorems.Thm_SZ_runXi_pos
import Theorems.Thm_SZ_run_even_floor

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) : treeXi β ∈ witnessSet :=
  ⟨runXi_pos (tree_isRun β), fun _ hn =>
    run_even_floor (tree_isRun β) (tree_exists_fst_eq_zero β) (tree_exists_snd_eq_two β) hn⟩
end SZ
