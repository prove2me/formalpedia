-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialRightTailProbThird_le_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:09.151658+00:00
-- url     : https://prove2.me/submissions/cc7391e0-9fef-4e03-aa80-1c8fc4bc0894

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_binomialMassThird_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_binomialExpMomentThird_eq
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution (n rOut : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialRightTailProbThird n rOut ≤
      Real.exp (-(lam * (rOut : ℝ))) *
        (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by
  unfold binomialRightTailProbThird
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if rOut < i then binomialMassThird n i else 0) ≤
        Real.exp (-(lam * (rOut : ℝ))) *
          (binomialMassThird n i * (Real.exp lam) ^ i) := by
    intro i _hi
    by_cases hright : rOut < i
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hfactor_ge_one :
          1 ≤ Real.exp (-(lam * (rOut : ℝ))) * (Real.exp lam) ^ i := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        have hle_real : (rOut : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_lt hright)
        have harg : 0 ≤ lam * ((i : ℝ) - rOut) :=
          mul_nonneg hlam (sub_nonneg.mpr hle_real)
        have heq : -(lam * (rOut : ℝ)) + (i : ℝ) * lam =
            lam * ((i : ℝ) - rOut) := by ring
        simp_all
      calc
        (if rOut < i then binomialMassThird n i else 0)
            = binomialMassThird n i := by simp [hright]
        _ ≤ binomialMassThird n i *
              (Real.exp (-(lam * (rOut : ℝ))) * (Real.exp lam) ^ i) :=
            le_mul_of_one_le_right hmass_nonneg hfactor_ge_one
        _ = Real.exp (-(lam * (rOut : ℝ))) *
              (binomialMassThird n i * (Real.exp lam) ^ i) := by ring
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hpow_nonneg : 0 ≤ (Real.exp lam) ^ i :=
        pow_nonneg (Real.exp_nonneg _) i
      have hrhs_nonneg :
          0 ≤ Real.exp (-(lam * (rOut : ℝ))) *
            (binomialMassThird n i * (Real.exp lam) ^ i) :=
        mul_nonneg (Real.exp_nonneg _) (mul_nonneg hmass_nonneg hpow_nonneg)
      simpa [hright] using hrhs_nonneg
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ i ∈ Finset.range (n + 1),
        if rOut < i then binomialMassThird n i else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
          Real.exp (-(lam * (rOut : ℝ))) *
            (binomialMassThird n i * (Real.exp lam) ^ i) := hsum
    _ = Real.exp (-(lam * (rOut : ℝ))) *
        (∑ i ∈ Finset.range (n + 1),
          binomialMassThird n i * (Real.exp lam) ^ i) := by
          rw [Finset.mul_sum]
    _ = Real.exp (-(lam * (rOut : ℝ))) *
        (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by
          rw [binomialExpMomentThird_eq]
end PebblingLean.Hypercube
