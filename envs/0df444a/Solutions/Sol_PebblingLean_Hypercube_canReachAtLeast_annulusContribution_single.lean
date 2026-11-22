-- Prove2me | solution 1 for PebblingLean.Hypercube.canReachAtLeast_annulusContribution_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:48.512798+00:00
-- url     : https://prove2.me/submissions/779b9365-128d-4121-9073-df55b026d125

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
public import Theorems.Thm_PebblingLean_Hypercube_annulusContribution_eq_of_mem
public import Theorems.Thm_PebblingLean_Hypercube_canReachAtLeast_single_dist
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
attribute [local simp] PebblingLean.Hypercube.mem_annulus



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    CanReachAtLeast (graph n)
      (Pebbling.single center (2 ^ rOut)) target
      (annulusContribution rIn rOut target center) := by
  have hbounds := mem_annulus.mp hmem
  have hcontrib :
      annulusContribution rIn rOut target center =
        2 ^ (rOut - dist center target) :=
    annulusContribution_eq_of_mem hmem
  have hsize :
      2 ^ rOut =
        annulusContribution rIn rOut target center * 2 ^ dist center target := by
    rw [hcontrib, ← Nat.pow_add]
    rw [Nat.sub_add_cancel hbounds.2]
  rw [hsize]
  exact canReachAtLeast_single_dist center target
    (annulusContribution rIn rOut target center)
end PebblingLean.Hypercube
