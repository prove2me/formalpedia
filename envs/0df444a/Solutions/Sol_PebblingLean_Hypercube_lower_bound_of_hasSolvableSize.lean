-- Prove2me | solution 1 for PebblingLean.Hypercube.lower_bound_of_hasSolvableSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:35.448742+00:00
-- url     : https://prove2.me/submissions/d57046ec-7b6d-4741-9d42-324fcffe43e9

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
public import Theorems.Thm_PebblingLean_Hypercube_lower_bound_size_of_solvable

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n k : ℕ}
    (h : HasSolvableSize (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) := by
  rcases h with ⟨D, hsize, hsolv⟩
  rw [← hsize]
  exact lower_bound_size_of_solvable hsolv
end PebblingLean.Hypercube
