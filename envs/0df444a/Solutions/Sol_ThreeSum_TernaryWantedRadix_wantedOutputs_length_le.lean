-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.wantedOutputs_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:00.639813+00:00
-- url     : https://prove2.me/submissions/465574a2-85a0-4663-ac45-50969232b63d

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket
namespace ThreeSum.TernaryWantedRadix
open Finset
private theorem flatMap_length_le {A B : Type*} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith
end ThreeSum.TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) (C : ℕ)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) :
    ∀ j x, (wantedOutputs p raws j x).length ≤ C^j := by
  intro j
  induction j with
  | zero => intro x; simp [wantedOutputs]
  | succ j ih =>
    intro x
    calc
      _ ≤ (localBucket p raws x).length*C^j :=
        flatMap_length_le _ _ _ (fun i _ => by simpa using ih ((x-raws.getD i 0)/p))
      _ ≤ C*C^j := Nat.mul_le_mul_right _ (hcap x)
      _ = _ := (pow_succ' _ _).symm
end ThreeSum.TernaryWantedRadix
