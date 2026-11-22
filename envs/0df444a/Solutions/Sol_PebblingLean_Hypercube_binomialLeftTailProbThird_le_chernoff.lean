-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialLeftTailProbThird_le_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:07.497885+00:00
-- url     : https://prove2.me/submissions/6dc908f4-8891-4e1f-9cf8-187124312542

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_binomialMassThird_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_binomialExpNegMomentThird_eq
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
theorem _root_.solution (n rIn : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialLeftTailProbThird n rIn ≤
      Real.exp (lam * (rIn : ℝ)) *
        (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
  unfold binomialLeftTailProbThird
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if i < rIn then binomialMassThird n i else 0) ≤
        Real.exp (lam * (rIn : ℝ)) *
          (binomialMassThird n i * (Real.exp (-lam)) ^ i) := by
    intro i _hi
    by_cases hleft : i < rIn
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hfactor_ge_one :
          1 ≤ Real.exp (lam * (rIn : ℝ)) * (Real.exp (-lam)) ^ i := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        have hle_real : (i : ℝ) ≤ rIn := by exact_mod_cast (Nat.le_of_lt hleft)
        have harg : 0 ≤ lam * ((rIn : ℝ) - i) :=
          mul_nonneg hlam (sub_nonneg.mpr hle_real)
        have heq : lam * (rIn : ℝ) + (i : ℝ) * -lam =
            lam * ((rIn : ℝ) - i) := by ring
        simp_all
      calc
        (if i < rIn then binomialMassThird n i else 0)
            = binomialMassThird n i := by simp [hleft]
        _ ≤ binomialMassThird n i *
              (Real.exp (lam * (rIn : ℝ)) * (Real.exp (-lam)) ^ i) :=
            le_mul_of_one_le_right hmass_nonneg hfactor_ge_one
        _ = Real.exp (lam * (rIn : ℝ)) *
              (binomialMassThird n i * (Real.exp (-lam)) ^ i) := by ring
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hpow_nonneg : 0 ≤ (Real.exp (-lam)) ^ i :=
        pow_nonneg (Real.exp_nonneg _) i
      have hrhs_nonneg :
          0 ≤ Real.exp (lam * (rIn : ℝ)) *
            (binomialMassThird n i * (Real.exp (-lam)) ^ i) :=
        mul_nonneg (Real.exp_nonneg _) (mul_nonneg hmass_nonneg hpow_nonneg)
      simpa [hleft] using hrhs_nonneg
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ i ∈ Finset.range (n + 1),
        if i < rIn then binomialMassThird n i else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
          Real.exp (lam * (rIn : ℝ)) *
            (binomialMassThird n i * (Real.exp (-lam)) ^ i) := hsum
    _ = Real.exp (lam * (rIn : ℝ)) *
        (∑ i ∈ Finset.range (n + 1),
          binomialMassThird n i * (Real.exp (-lam)) ^ i) := by
          rw [Finset.mul_sum]
    _ = Real.exp (lam * (rIn : ℝ)) *
        (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
          rw [binomialExpNegMomentThird_eq]
end PebblingLean.Hypercube
