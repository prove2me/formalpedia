-- Prove2me | solution 1 for SoficGroups.one_mem_finiteBlockCoefficientSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/a5bfe8e7-30e3-4617-9b85-0d226cd8ea08

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution (s : Finset R) :
    (1 : R) ∈ finiteBlockCoefficientSpan s := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ (Set.mem_singleton 1)
end SoficGroups
