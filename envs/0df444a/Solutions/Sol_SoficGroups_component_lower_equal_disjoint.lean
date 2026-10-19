-- Prove2me | solution 1 for SoficGroups.component_lower_equal_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/7f93c67a-f956-493f-ac6a-c6e7408e013e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) :
    Disjoint (C.filter fun z => b z < b x)
      (C.filter fun z => b z = b x) := by
  apply Finset.disjoint_left.mpr
  intro z hzlow hzeq
  have hlow := (Finset.mem_filter.mp hzlow).2
  have heq := (Finset.mem_filter.mp hzeq).2
  omega
end SoficGroups
