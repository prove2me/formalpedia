-- Prove2me | solution 1 for SoficGroups.componentVertexMidrank_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/de0ebf81-7d29-459c-bc9f-69c98f213acd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    0 ≤ componentVertexMidrank C b x := by
  unfold componentVertexMidrank
  positivity
end SoficGroups
