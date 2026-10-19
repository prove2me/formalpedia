-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.retainedComponents_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/10165cc5-fddc-4255-a282-ec4b4909de24

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_maximumOverlapPart_mem
import Theorems.Thm_SoficGroups_maximumOverlapPart_overlap_of_not_mem_insufficient

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
    (T : Equiv.Perm V) (b : V → ℤ) (eta : ℝ)
    (C : Finset V)
    (hC : C ∈ retainedComponents P Q T b eta) :
    C ∈ P.parts ∧
      SoficGroups.maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ) ∧
      ∃ y ∈ C ∩ SoficGroups.maximumOverlapPart Q C,
        b (T.symm y) = b y := by
  have hmem := Finset.mem_sdiff.mp hC
  have hpart : C ∈ P.parts := hmem.1
  have hnotbad : C ∉ SoficGroups.insufficientOverlapComponents P Q eta :=
    fun h => hmem.2 (Finset.mem_union_left _ h)
  have hnotwitnessless : C ∉ witnesslessComponents P Q T b eta :=
    fun h => hmem.2 (Finset.mem_union_right _ h)
  have htarget : SoficGroups.maximumOverlapPart Q C ∈ Q.parts :=
    SoficGroups.maximumOverlapPart_mem Q C
      (P.nonempty_of_mem_parts hpart) (P.subset hpart)
  have hoverlap :=
    SoficGroups.maximumOverlapPart_overlap_of_not_mem_insufficient
      P Q eta C hpart hnotbad
  refine ⟨hpart, htarget, hoverlap, ?_⟩
  by_contra hnone
  push Not at hnone
  apply hnotwitnessless
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hpart, hnotbad⟩, hnone⟩
end SoficGroups.SourceCompressionRetainedDiscard
