-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.witnesslessComponents_subset_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/4c007fa6-99fa-4638-bf8f-6a26bfedc9fd

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionRetainedDiscard
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ) :
    witnesslessComponents P Q T b eta ⊆ P.parts := by
  intro C hC
  exact (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hC).1).1
end SoficGroups.SourceCompressionRetainedDiscard
