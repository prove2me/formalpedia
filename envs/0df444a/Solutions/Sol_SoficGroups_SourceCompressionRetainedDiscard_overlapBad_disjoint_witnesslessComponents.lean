-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.overlapBad_disjoint_witnesslessComponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/4762031c-c517-4adc-9c1e-3d4b19a7a8c2

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
    Disjoint (SoficGroups.insufficientOverlapComponents P Q eta)
      (witnesslessComponents P Q T b eta) := by
  apply Finset.disjoint_left.mpr
  intro C hbad hwitnessless
  exact (Finset.mem_sdiff.mp
    (Finset.mem_filter.mp hwitnessless).1).2 hbad
end SoficGroups.SourceCompressionRetainedDiscard
