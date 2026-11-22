-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusContribution_sq_le_width_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:54.161808+00:00
-- url     : https://prove2.me/submissions/8446c563-ce1b-4108-9d49-dadf21382aef

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Hypercube_annulusContribution_le_width

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ^ 2 ≤
      2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
  have hle := annulusContribution_le_width (rIn := rIn) (rOut := rOut) target center
  calc
    annulusContribution rIn rOut target center ^ 2
        = annulusContribution rIn rOut target center *
          annulusContribution rIn rOut target center := by
          rw [pow_two]
    _ ≤ annulusContribution rIn rOut target center * 2 ^ (rOut - rIn) := by
          exact Nat.mul_le_mul_left _ hle
    _ = 2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
          rw [Nat.mul_comm]
end PebblingLean.Hypercube
