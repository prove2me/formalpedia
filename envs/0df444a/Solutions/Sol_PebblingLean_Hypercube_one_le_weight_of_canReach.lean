-- Prove2me | solution 1 for PebblingLean.Hypercube.one_le_weight_of_canReach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:18.714786+00:00
-- url     : https://prove2.me/submissions/a50aadef-7f9f-4ab5-bbe9-e3c67a066274

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
public import Theorems.Thm_PebblingLean_Hypercube_dist_adj_le_succ
public import Theorems.Thm_PebblingLean_Pebbling_one_le_weight_of_canReach


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    {target : HypercubeVertex n}
    (hcan : CanReach (graph n) D target) :
    1 ≤ weight dist D target := by
  exact Pebbling.one_le_weight_of_canReach (G := graph n) (dist := dist)
    (D := D) (target := target) hcan (dist_self target)
    (fun {u v} h => dist_adj_le_succ (t := target) h)
end PebblingLean.Hypercube
