-- Prove2me | solution 1 for SZ.tree_exists_branching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:38.997893+00:00
-- url     : https://prove2.me/submissions/cc44dba4-7351-4948-85ef-4c91ed9863e9

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gState_add
import Theorems.Thm_SZ_gStart_gState
import Theorems.Thm_SZ_gExists_snd_eq_two
import Theorems.Thm_SZ_gExists_fst_eq_zero
import Theorems.Thm_SZ_gExists_inO
import Theorems.Thm_SZ_node_succ
import Theorems.Thm_SZ_tree_gStart
import Theorems.Thm_SZ_node_st_of_not_branching
import Theorems.Thm_P2M_SZ_treeDigit_of_not_branching__22c03d651ba9
import Theorems.Thm_SZ_node_g0_mono
import Theorems.Thm_SZ_node_g2_mono

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (N : ℕ) : ∃ k, N ≤ k ∧ Branching (node β k) := by
  by_contra hcon
  push Not at hcon
  have hno : ∀ i, ¬ Branching (node β (N + i)) := fun i => hcon _ (Nat.le_add_right _ _)
  have hstart : GStart (node β N).st := tree_gStart β N
  obtain ⟨k0, hk0⟩ := gExists_fst_eq_zero hstart
  obtain ⟨k2, hk2⟩ := gExists_snd_eq_two hstart
  have hd0 : (treeDigit β (N + k0)).1 = 0 := by
    rw [treeDigit_of_not_branching' β hno k0]; exact hk0
  have hd2 : (treeDigit β (N + k2)).2 = 2 := by
    rw [treeDigit_of_not_branching' β hno k2]; exact hk2
  have hset0 : (node β (N + (k0 + 1))).g0 = true := by
    have e : N + (k0 + 1) = (N + k0) + 1 := by omega
    rw [e, node_succ, nodeNext, if_neg (hno k0)]
    show ((node β (N + k0)).g0 || decide ((treeDigit β (N + k0)).1 = 0)) = true
    simp [hd0]
  have hset2 : (node β (N + (k2 + 1))).g2 = true := by
    have e : N + (k2 + 1) = (N + k2) + 1 := by omega
    rw [e, node_succ, nodeNext, if_neg (hno k2)]
    show ((node β (N + k2)).g2 || decide ((treeDigit β (N + k2)).2 = 2)) = true
    simp [hd2]
  obtain ⟨k3, hk3⟩ := gExists_inO (gStart_gState hstart (max (k0 + 1) (k2 + 1)))
  set t := max (k0 + 1) (k2 + 1) with ht
  refine hno (t + k3) ⟨node_g0_mono β hno (show k0 + 1 ≤ t + k3 by omega) hset0,
    node_g2_mono β hno (show k2 + 1 ≤ t + k3 by omega) hset2, ?_⟩
  rw [node_st_of_not_branching β hno, gState_add]
  exact hk3
end SZ
