-- Prove2me | solution 1 for SoficGroups.mem_finiteBlockCoefficientSpan_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/cb97cce9-d112-4b46-89b2-1e8212d0b498

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (s : Finset R) {a : R} (ha : a ∈ s) :
    a ∈ finiteBlockCoefficientSpan s := by
  apply Submodule.subset_span
  exact Set.mem_union_right _ ha
end SoficGroups
