-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.mem_wantedOutputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:26.136681+00:00
-- url     : https://prove2.me/submissions/545786f3-734c-4a8b-9cb3-e85d785beaa1

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_7c515d7a0181c20c
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x is, is ∈ wantedOutputs p raws j x ↔
      is.length=j ∧ (∀ i ∈ is, i < raws.length) ∧
      p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is := by
  intro j
  induction j with
  | zero => intro x is; cases is <;> simp [wantedOutputs,Radix.positionalHash]
  | succ j ih =>
    intro x is
    cases is with
    | nil => simp [wantedOutputs]
    | cons i is =>
      simp only [wantedOutputs,List.mem_flatMap,List.mem_map,List.cons.injEq]
      have he : (∃ a ∈ localBucket p raws x, ∃ ys ∈ wantedOutputs p raws j ((x-raws.getD a 0)/p),
          a=i ∧ ys=is) ↔
          i ∈ localBucket p raws x ∧ is ∈ wantedOutputs p raws j ((x-raws.getD i 0)/p) := by
        aesop
      rw [he,mem_localBucket,ih]
      simp only [List.length_cons,Nat.add_right_cancel_iff,List.mem_cons,forall_eq_or_imp,
        Radix.positionalHash,Radix.radix_divisibility p _ _ _ hp]
      tauto
end ThreeSum.TernaryWantedRadix
