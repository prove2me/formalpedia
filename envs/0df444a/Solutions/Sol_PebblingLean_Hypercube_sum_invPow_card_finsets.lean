-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_invPow_card_finsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:46.727111+00:00
-- url     : https://prove2.me/submissions/5329c13e-8236-4b2b-9ce9-3b9cbb0b7fef

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
theorem _root_.solution (n : ℕ) :
    (∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card) = ((3 : ℚ) / 2) ^ n := by
  classical
  have h := Finset.prod_add (s := (Finset.univ : Finset (Fin n)))
    (f := fun _ : Fin n => (1 : ℚ) / 2) (g := fun _ : Fin n => (1 : ℚ))
  norm_num [Finset.prod_const, Finset.powerset_univ, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc, add_comm, add_left_comm, add_assoc] at h
  calc
    (∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card) = (2 ^ n : ℚ)⁻¹ * 3 ^ n := by
      simpa [div_eq_mul_inv] using h.symm
    _ = ((3 : ℚ) / 2) ^ n := by
      rw [div_pow]
      ring
end PebblingLean.Hypercube
