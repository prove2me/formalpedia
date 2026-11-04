-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.child_target_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:08.330289+00:00
-- url     : https://prove2.me/submissions/dffd473c-434e-4d76-a99b-c4ee1c96e7c1

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
theorem _root_.solution (p V : ℕ) (hp : 2 ≤ p) {x a : ℤ}
    (hx : |x| ≤ (V : ℤ)) (ha : |a| ≤ (V : ℤ)) (hdiv : (p : ℤ) ∣ x-a) :
    |(x-a)/(p : ℤ)| ≤ (V : ℤ) := by
  have he := Int.mul_ediv_cancel' hdiv
  have hh : |x-a| ≤ 2*(V : ℤ) := by
    have h : |x-a| ≤ |x|+|a| := by simpa using abs_sub_le x 0 a
    linarith
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hpn : (0 : ℤ) ≤ p := by positivity
  have he' : |x-a| = (p : ℤ)*|(x-a)/(p : ℤ)| := by nth_rewrite 1 [← he]; rw [abs_mul,abs_of_nonneg hpn]
  nlinarith [abs_nonneg ((x-a)/(p : ℤ))]
end ThreeSum.TernaryWantedRadix
