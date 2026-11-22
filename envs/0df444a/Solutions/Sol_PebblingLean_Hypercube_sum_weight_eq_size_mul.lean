-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_weight_eq_size_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:02.689827+00:00
-- url     : https://prove2.me/submissions/2a8b2046-994d-4e21-b837-3aa8d8331720

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
public import Theorems.Thm_PebblingLean_Hypercube_sum_unitWeight
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
theorem _root_.solution {n : ℕ} (D : Pebbling (HypercubeVertex n)) :
    (∑ target : HypercubeVertex n, weight dist D target)
      = (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
  classical
  calc
    (∑ target : HypercubeVertex n, weight dist D target)
        = ∑ target : HypercubeVertex n,
            ∑ u : HypercubeVertex n, (D u : ℚ) * unitWeight dist target u := by
          rfl
    _ = ∑ u : HypercubeVertex n,
            ∑ target : HypercubeVertex n, (D u : ℚ) * unitWeight dist target u := by
          exact Finset.sum_comm
    _ = ∑ u : HypercubeVertex n,
            (D u : ℚ) * (∑ target : HypercubeVertex n, unitWeight dist target u) := by
          simp [Finset.mul_sum]
    _ = ∑ u : HypercubeVertex n, (D u : ℚ) * ((3 : ℚ) / 2) ^ n := by
          simp [sum_unitWeight]
    _ = (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
          simp [size, Finset.sum_mul]
end PebblingLean.Hypercube
