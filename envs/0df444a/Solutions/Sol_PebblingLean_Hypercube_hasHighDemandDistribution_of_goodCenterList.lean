-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_of_goodCenterList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:20.834654+00:00
-- url     : https://prove2.me/submissions/1305ee4b-8abb-409d-be5a-5597f5813b71

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
public import Theorems.Thm_PebblingLean_Hypercube_size_stackListDistribution
public import Theorems.Thm_PebblingLean_Hypercube_minOccupiedPileSize_stackListDistribution
public import Theorems.Thm_PebblingLean_Hypercube_solvableAtLeast_stackListDistribution_of_good

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
    HasHighDemandDistribution n T (centers.length * 2 ^ rOut) (2 ^ rOut) := by
  refine ⟨stackListDistribution rOut centers, ?_, ?_, ?_⟩
  · rw [size_stackListDistribution]
  · exact solvableAtLeast_stackListDistribution_of_good hgood
  · exact minOccupiedPileSize_stackListDistribution centers
end PebblingLean.Hypercube
