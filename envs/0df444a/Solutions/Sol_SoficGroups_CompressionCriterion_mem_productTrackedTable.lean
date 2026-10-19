-- Prove2me | solution 1 for SoficGroups.CompressionCriterion.mem_productTrackedTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/93c2759e-07ea-46db-a21a-a309b225fac8

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
    {F : Finset J} {j : J} (hj : j ∈ F) :
    j ∈ productTrackedTable F := by
  classical
  exact SoficGroups.mem_multiplicationTable_of_mem
    (Finset.mem_insert_of_mem hj)
end SoficGroups.CompressionCriterion
