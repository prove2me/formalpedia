-- Prove2me | solution 1 for PebblingLean.Hypercube.card_le_size_mul_of_solvable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:21.395907+00:00
-- url     : https://prove2.me/submissions/1f7e4d1b-2a58-4216-8fad-b27cd739c820

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
public import Theorems.Thm_PebblingLean_Hypercube_card_le_sum_weight_of_solvable
public import Theorems.Thm_PebblingLean_Hypercube_sum_weight_eq_size_mul

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    (Fintype.card (HypercubeVertex n) : ℚ) ≤
      (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by
  exact (card_le_sum_weight_of_solvable (D := D) hsolv).trans_eq
    (sum_weight_eq_size_mul D)
end PebblingLean.Hypercube
