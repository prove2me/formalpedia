-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.exists_terminal_iterate_of_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:57:16.6138+00:00
-- url     : https://prove2.me/submissions/51e6ab72-4900-4b33-b791-457d20316be6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {n0 : ℕ}
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n) (n : ℕ) :
    ∃ k : ℕ, ActiveFor next n0 k n ∧ iterate next k n < n0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < n0
      · exact ⟨0, trivial, hn⟩
      · have hn0 : n0 ≤ n := Nat.le_of_not_gt hn
        rcases ih (next n) (hnext n hn0) with ⟨k, hactive, hterminal⟩
        exact ⟨k + 1, ⟨hn0, hactive⟩, by simpa [iterate] using hterminal⟩
end PebblingLean.Hypercube.LossRecurrence
