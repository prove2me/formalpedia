-- Prove2me | solution 1 for PebblingLean.Hypercube.lower_bound_size_of_solvable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:57.808862+00:00
-- url     : https://prove2.me/submissions/57b5015b-d26f-42d9-bfa6-d920d83b54fa

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Theorems.Thm_PebblingLean_Hypercube_card_le_size_mul_of_solvable
public import Theorems.Thm_PebblingLean_Hypercube_card_vertex
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.weight_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    ((4 : ℚ) / 3) ^ n ≤ (size D : ℚ) := by
  have h := card_le_size_mul_of_solvable (D := D) hsolv
  simp only [card_vertex, Nat.cast_pow, Nat.cast_ofNat] at h
  have hpos : 0 < ((3 : ℚ) / 2) ^ n := by positivity
  have hdiv : ((2 : ℚ) ^ n) / (((3 : ℚ) / 2) ^ n) ≤ (size D : ℚ) := by
    exact (div_le_iff₀ hpos).mpr h
  have heq : ((4 : ℚ) / 3) ^ n = ((2 : ℚ) ^ n) / (((3 : ℚ) / 2) ^ n) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num]
    rw [div_pow, div_pow]
    field_simp
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simpa [heq]
end PebblingLean.Hypercube
