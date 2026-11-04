-- Prove2me | solution 1 for ThreeSum.RawReporting.mem_frontier_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:33.584046+00:00
-- url     : https://prove2.me/submissions/2bc06059-dc08-4ae5-aa86-db59051785e0

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_WeightedCache3SUM_Alias_658daccd3d316101
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Reporting_mass_pos_iff
import Definitions.Def_WeightedCache3SUM_Alias_c2dccdb99e31a4aa
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawReporting
theorem _root_.solution {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) (pre : List (Finset (Fin (512 * h)))) :
    pre ∈ frontier I w k ↔ ∃ r ∈ I, wantedOf r = w ∧ (word r).take k = pre := by
  rw [frontier, Reporting.mem_frontier_iff (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) hk]
  rw [Reporting.mass_pos_iff]
  simp only [domain, Finset.mem_filter, Nat.lt_one_iff, and_true]
  constructor
  · rintro ⟨r, ⟨hr, hw⟩, hp⟩
    exact ⟨r, hr, hw, hp⟩
  · rintro ⟨r, hr, hw, hp⟩
    exact ⟨r, ⟨hr, hw⟩, hp⟩
end ThreeSum.RawReporting
