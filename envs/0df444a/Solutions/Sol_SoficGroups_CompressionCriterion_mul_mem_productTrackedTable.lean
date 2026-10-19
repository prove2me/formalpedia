-- Prove2me | solution 1 for SoficGroups.CompressionCriterion.mul_mem_productTrackedTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5b205d2d-7161-48ca-9f7f-b2847ad28894

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
open SoficGroups.CompressionCriterion
open Filter Topology
namespace SoficGroups.CompressionCriterion
theorem _root_.solution {J : Type*} [Group J]
    {F : Finset J} {x y : J} (hx : x ∈ F) (hy : y ∈ F) :
    x * y ∈ productTrackedTable F := by
  classical
  exact SoficGroups.mul_mem_multiplicationTable
    (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
end SoficGroups.CompressionCriterion
