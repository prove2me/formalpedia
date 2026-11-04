-- Prove2me | solution 1 for ThreeSum.TernaryPartitionCount.canonical_output_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:57.07548+00:00
-- url     : https://prove2.me/submissions/97a44bb3-135f-444e-b427-61c3936f2a20

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Theorems.Thm_ThreeSum_TernaryPartitionCount_canonicalEdge_injective
import Definitions.Def_WeightedCache3SUM_Alias_b7deb5218012ad6d
import Theorems.Thm_ThreeSum_LayerCounts_vertices_card


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound
namespace ThreeSum.TernaryPartitionCount
theorem _root_.solution (t r s : ℕ) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s)) := by
  classical
  let f : Parts r s → outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s) :=
    fun c => ⟨canonicalEdge c,rfl⟩
  have hf : Function.Injective f := fun _ _ h => canonicalEdge_injective (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  have hc : Fintype.card (Parts r s) =
      (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) := by
    rw [Fintype.card_prod]
    rw [Fintype.card_coe,Fintype.card_coe]
    rw [LayerCounts.vertices_card,LayerCounts.edgeSet_card]
  rw [hc] at h
  exact h
end ThreeSum.TernaryPartitionCount
