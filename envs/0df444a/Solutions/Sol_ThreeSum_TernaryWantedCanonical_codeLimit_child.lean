-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonical.codeLimit_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:39.833005+00:00
-- url     : https://prove2.me/submissions/de03e78d-c04e-4e77-8e2d-eb0b69838749

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonical
theorem _root_.solution {N code R j digit : ℕ} (hN : 1 ≤ N) (hdigit : digit < R) :
    codeLimit N (code*R+digit) R j ≤ codeLimit N code R (j+1) := by
  unfold codeLimit
  rw [pow_succ']
  have h : code*R+digit+R ≤ (code+R)*(2*(N+R)) := by nlinarith
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((2*(N+R))^j) h
end ThreeSum.TernaryWantedCanonical
