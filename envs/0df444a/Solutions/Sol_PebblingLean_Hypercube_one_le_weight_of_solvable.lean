-- Prove2me | solution 1 for PebblingLean.Hypercube.one_le_weight_of_solvable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:07.970802+00:00
-- url     : https://prove2.me/submissions/fa0cad69-4dcc-40ac-bee5-6ac34c1c2bc0

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
public import Theorems.Thm_PebblingLean_Hypercube_one_le_weight_of_canReach
public import Theorems.Thm_PebblingLean_Pebbling_one_le_weight_of_canReach


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) (target : HypercubeVertex n) :
    1 ≤ weight dist D target :=
  one_le_weight_of_canReach (D := D) (target := target) (hsolv target)
end PebblingLean.Hypercube
