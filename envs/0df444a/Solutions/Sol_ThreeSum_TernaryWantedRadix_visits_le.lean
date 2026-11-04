-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.visits_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:22.640738+00:00
-- url     : https://prove2.me/submissions/07545a28-340c-49b0-89d0-3ba5f2049579

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

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) :
    ∀ j x, visits p raws j x ≤ (j+1)*C^j := by
  intro j
  induction j with
  | zero => intro x; simp [visits]
  | succ j ih =>
    intro x
    have hs : ((localBucket p raws x).map fun i => visits p raws j ((x-raws.getD i 0)/p)).sum ≤
        (localBucket p raws x).length*((j+1)*C^j) := by
      induction localBucket p raws x with
      | nil => simp
      | cons i is ih' =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        have h := ih ((x-raws.getD i 0)/p)
        nlinarith
    have hb := Nat.mul_le_mul_right ((j+1)*C^j) (hcap x)
    have hp := one_le_pow₀ hC (n := j+1)
    simp only [visits]
    rw [pow_succ'] at hp ⊢
    nlinarith
end ThreeSum.TernaryWantedRadix
