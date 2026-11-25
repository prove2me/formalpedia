-- Prove2me | solution 1 for SZ.runXi_treeDigit_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:51.184262+00:00
-- url     : https://prove2.me/submissions/5a2a517c-2f1b-4abb-adc4-a1e0f8569299

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_branchDigit_fst_ne
import Theorems.Thm_SZ_tree_isRun
import Theorems.Thm_SZ_treeDigit_of_branching
import Theorems.Thm_SZ_isDigits_run_fst
import Theorems.Thm_SZ_digitReal_ne
import Theorems.Thm_SZ_node_used_mono
import Theorems.Thm_SZ_exists_branch_at_used
import Theorems.Thm_SZ_node_congr
import Theorems.Thm_SZ_treeDigit_congr

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    Function.Injective (fun β : ℕ → Bool => runXi (treeDigit β)) := by
  classical
  intro β β' heq
  by_contra hne
  have hex : ∃ i, β i ≠ β' i := by
    by_contra hx
    push Not at hx
    exact hne (funext hx)
  set n := Nat.find hex with hn
  have hbit : β n ≠ β' n := Nat.find_spec hex
  have hagree : ∀ i, i < n → β i = β' i := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  obtain ⟨k, hku, hkb⟩ := exists_branch_at_used β n
  -- the two plays agree before step `k` and differ there
  have hbefore : ∀ j, j < k → (treeDigit β j).1 = (treeDigit β' j).1 := by
    intro j hj
    have : (node β (j + 1)).used ≤ n := by
      rw [← hku]; exact node_used_mono β (by omega)
    rw [treeDigit_congr hagree this]
  have hdiff : (treeDigit β k).1 ≠ (treeDigit β' k).1 := by
    have heqn : node β k = node β' k := node_congr hagree k (by omega)
    rw [treeDigit_of_branching β hkb,
      treeDigit_of_branching β' (by rw [← heqn]; exact hkb), ← heqn, hku]
    exact branchDigit_fst_ne hbit
  -- so the `a`-streams differ, hence the witnesses do
  have hx : digitReal 3 (fun i => (treeDigit β i).1) ≠ digitReal 3 (fun i => (treeDigit β' i).1) :=
    digitReal_ne (isDigits_run_fst (tree_isRun β)) (isDigits_run_fst (tree_isRun β'))
      (fun j => (tree_isRun β j).1.1) (fun j => (tree_isRun β' j).1.1) hbefore hdiff
  have := heq
  simp only [runXi] at this
  exact hx (by linarith [this])
end SZ
