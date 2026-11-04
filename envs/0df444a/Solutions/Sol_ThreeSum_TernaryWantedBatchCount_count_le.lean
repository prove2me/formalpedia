-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchCount.count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:58.811333+00:00
-- url     : https://prove2.me/submissions/8be8d56d-12ae-4ba3-8527-2b45fdfdee34

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Theorems.Thm_ThreeSum_TernaryWantedBatchCount_rows_length
import Theorems.Thm_ThreeSum_LightTernaryWantedBatch_rows_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedBatchCount
open LightTernaryWantedBatch TernaryWantedLittleEndian LightTernaryWantedCanonical
namespace ThreeSum.TernaryWantedBatchCount
theorem _root_.solution (p R S J C : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (targets : ℕ → ℤ) (positions : ℕ → ℕ)
    (hcap : ∀ x, (TernaryWantedRadix.localBucket (p : ℤ) raws x).length≤C) (n : ℕ) :
    count p R S J raws words maps targets n≤n*C^J := by
  have hh := LightTernaryWantedBatch.rows_length_le p R S J C raws words maps targets positions hcap n
  rw [rows_length] at hh
  nlinarith
end ThreeSum.TernaryWantedBatchCount
