-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:00.574186+00:00
-- url     : https://prove2.me/submissions/d77bbf32-150b-4117-99cf-7126c5dd904b

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
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (k n : ℕ) (hactive : ActiveFor next n0 k n) :
    R n ≤ lossProduct next loss k n * R (iterate next k n) := by
  revert n
  induction k with
  | zero =>
      intro n _hactive
      simp [lossProduct, iterate]
  | succ k ih =>
      intro n hactive
      rcases hactive with ⟨hn, htail⟩
      have htail_le := ih (next n) htail
      have hfactor_nonneg : 0 ≤ 1 + loss n :=
        add_nonneg zero_le_one (hloss n)
      have htail_mul :
          (1 + loss n) * R (next n) ≤
            (1 + loss n) *
              (lossProduct next loss k (next n) *
                R (iterate next k (next n))) :=
        mul_le_mul_of_nonneg_left htail_le hfactor_nonneg
      calc
        R n ≤ (1 + loss n) * R (next n) := hstep n hn
        _ ≤ (1 + loss n) *
              (lossProduct next loss k (next n) *
                R (iterate next k (next n))) := htail_mul
        _ = lossProduct next loss (k + 1) n *
              R (iterate next (k + 1) n) := by
              simp [lossProduct, iterate, mul_assoc]
end PebblingLean.Hypercube.LossRecurrence
