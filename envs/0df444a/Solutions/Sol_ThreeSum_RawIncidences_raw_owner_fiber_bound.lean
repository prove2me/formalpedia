-- Prove2me | solution 1 for ThreeSum.RawIncidences.raw_owner_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:12.355911+00:00
-- url     : https://prove2.me/submissions/eb7bbd1f-c766-4b57-a2e1-14d6c5338230

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_witnesses_card_bound
import Theorems.Thm_ThreeSum_RawIncidences_mem_rawOn
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
theorem _root_.solution {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    ((rawOn h J P d T a b c).filter fun r => r.1 = t).card ≤ representationCap h J := by
  calc
    _ ≤ (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card := by
      apply Finset.card_le_card_of_injOn (fun r : RawItem h J α β γ => r.2)
      · intro r hr
        obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
        have hw := (mem_rawOn.mp hr).2
        simpa only [Finset.mem_coe, ht] using hw
      · intro r hr s hs he
        have hrt := (Finset.mem_filter.mp hr).2
        have hst := (Finset.mem_filter.mp hs).2
        exact Sigma.ext (hrt.trans hst.symm) (heq_of_eq he)
    _ ≤ _ := witnesses_card_bound hP hguard
end ThreeSum.RawIncidences
