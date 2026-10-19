-- Prove2me | solution 1 for SoficGroups.insufficientOverlapComponents_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/2a311821-d903-4a32-8630-07d03e83e47e

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
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) :
    insufficientOverlapComponents P Q eta ⊆ P.parts := by
  classical
  exact Finset.filter_subset _ _
end SoficGroups
