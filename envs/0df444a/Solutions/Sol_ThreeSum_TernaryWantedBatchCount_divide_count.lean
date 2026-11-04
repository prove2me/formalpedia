-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchCount.divide_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:59.682018+00:00
-- url     : https://prove2.me/submissions/fbb97fc7-4ee4-4b01-9a4f-7d3bc6528459

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Theorems.Thm_ThreeSum_TernaryWantedBatchCount_rows_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedBatchCount
open LightTernaryWantedBatch TernaryWantedLittleEndian LightTernaryWantedCanonical
namespace ThreeSum.TernaryWantedBatchCount
theorem _root_.solution (p R S J : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ) :
    (rows p R S J raws words maps targets positions n).length/3=
      count p R S J raws words maps targets n := by
  rw [rows_length,Nat.mul_div_right _ (by decide : 0<3)]
end ThreeSum.TernaryWantedBatchCount
