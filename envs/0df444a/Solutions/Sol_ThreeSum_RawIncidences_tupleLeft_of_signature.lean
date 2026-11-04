-- Prove2me | solution 1 for ThreeSum.RawIncidences.tupleLeft_of_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:51.483452+00:00
-- url     : https://prove2.me/submissions/98414ad0-5c8d-4dd3-b0ec-8c73ad09da65

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


namespace ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
private theorem positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : Radix.positionalHash p g (xs.map f) =
      Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Radix.positionalHash, ih]
section OriginalIndices
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
end OriginalIndices
end ThreeSum.RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {s t : ChoiceTuple h J}
    (he : leftSignature s = leftSignature t) : tupleLeft s = tupleLeft t := by
  have hraw : (fun i => rawLeft (s i)) = (fun i => rawLeft (t i)) := by
    funext i
    have hp := congrFun he i
    have ho := congrArg Prod.fst hp
    have hw := congrArg Prod.snd hp
    change occurrence (s i) = occurrence (t i) at ho
    change LocalGraph.left (edge (s i)) = LocalGraph.left (edge (t i)) at hw
    unfold rawLeft
    rw [ho, hw]
  have hl : (List.ofFn s).map rawLeft = (List.ofFn t).map rawLeft := by
    simpa only [List.map_ofFn, Function.comp_def] using congrArg List.ofFn hraw
  have hhash := congrArg (Radix.positionalHash (localPrime h) id) hl
  simpa only [positionalHash_map, id_eq, tupleLeft] using hhash
end ThreeSum.RawIncidences
