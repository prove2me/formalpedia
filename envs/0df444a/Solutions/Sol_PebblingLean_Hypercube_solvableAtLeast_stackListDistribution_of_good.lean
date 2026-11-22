-- Prove2me | solution 1 for PebblingLean.Hypercube.solvableAtLeast_stackListDistribution_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:33.751676+00:00
-- url     : https://prove2.me/submissions/e6b6c4fd-808f-4bb6-9114-f977b44e989f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Theorems.Thm_PebblingLean_Hypercube_canReachAtLeast_annulusTotalContribution_stackList
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_mono


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut T : ℕ}
    {centers : List (HypercubeVertex n)}
    (hgood : IsGoodCenterList n rIn rOut T centers) :
    SolvableAtLeast (graph n) (stackListDistribution rOut centers) T := by
  intro target
  exact Pebbling.canReachAtLeast_mono (hgood target)
    (canReachAtLeast_annulusTotalContribution_stackList target centers)
end PebblingLean.Hypercube
