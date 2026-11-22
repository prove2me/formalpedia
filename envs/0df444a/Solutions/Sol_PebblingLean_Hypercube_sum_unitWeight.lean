-- Prove2me | solution 1 for PebblingLean.Hypercube.sum_unitWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:23.484925+00:00
-- url     : https://prove2.me/submissions/5ae0bbc5-d422-41a7-97cc-b2c9008f5fb1

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
public import Theorems.Thm_PebblingLean_Hypercube_sum_invPow_card_finsets
public import Theorems.Thm_PebblingLean_Hypercube_dist_eq_card_diffSet
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
theorem _root_.solution (n : ℕ) (base : HypercubeVertex n) :
    (∑ target : HypercubeVertex n, unitWeight dist target base) = ((3 : ℚ) / 2) ^ n := by
  classical
  calc
    (∑ target : HypercubeVertex n, unitWeight dist target base)
        = ∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card := by
          simpa [unitWeight, dist_comm, dist_eq_card_diffSet, diffSetEquiv,
            Equiv.coe_fn_mk] using
            ((diffSetEquiv base).sum_comp
              (fun s : Finset (Fin n) => (1 : ℚ) / (2 : ℚ) ^ s.card))
    _ = ((3 : ℚ) / 2) ^ n := sum_invPow_card_finsets n
end PebblingLean.Hypercube
