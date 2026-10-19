-- Prove2me | solution 1 for SoficGroups.mem_permutationGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5d4476fe-0eb2-4b20-b18f-2621a644f04f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
namespace SoficGroups
theorem _root_.solution {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (x y : V) :
    (x, y) ∈ permutationGraph p ↔ y = p x := by
  simp [permutationGraph, eq_comm]
end SoficGroups
