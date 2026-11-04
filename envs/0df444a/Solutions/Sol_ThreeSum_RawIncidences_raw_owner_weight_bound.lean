-- Prove2me | solution 1 for ThreeSum.RawIncidences.raw_owner_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:16.458618+00:00
-- url     : https://prove2.me/submissions/d35a6a5a-9fce-4b66-bb6d-8fe717880eb5

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_raw_owner_fiber_bound
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
    Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t ≤
      representationCap h J := by
  have he : Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t =
      ((rawOn h J P d T a b c).filter fun r => r.1 = t).card := by
    simp only [Arithmetic.fiberWeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  exact raw_owner_fiber_bound T a b c hP hguard t
end ThreeSum.RawIncidences
