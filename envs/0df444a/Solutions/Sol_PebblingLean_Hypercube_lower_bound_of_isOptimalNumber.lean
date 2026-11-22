-- Prove2me | solution 1 for PebblingLean.Hypercube.lower_bound_of_isOptimalNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:26.515019+00:00
-- url     : https://prove2.me/submissions/dbf09bb8-abe2-4778-b74f-43525d1d2571

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
public import Theorems.Thm_PebblingLean_Hypercube_lower_bound_of_hasSolvableSize

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n k : ℕ}
    (hopt : IsOptimalNumber (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) :=
  lower_bound_of_hasSolvableSize hopt.1
end PebblingLean.Hypercube
