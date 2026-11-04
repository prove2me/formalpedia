-- Prove2me | solution 1 for ThreeSum.RawIncidences.leftBucket_of_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:35.956215+00:00
-- url     : https://prove2.me/submissions/a2b1bf53-a6ab-41ff-9fa5-43b5dc7ae7c8

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_tupleLeft_of_signature
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {s t : ChoiceTuple h J} (he : leftSignature s = leftSignature t) :
    leftBucket P B b s = leftBucket P B b t := by
  simp only [leftBucket, tupleLeft_of_signature he]
end ThreeSum.RawIncidences
