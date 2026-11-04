-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchIndex.read_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:08.652892+00:00
-- url     : https://prove2.me/submissions/73a25ce9-cd86-4cc8-911f-d21670409e61

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_cells_entries_eq_rows
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_read_three
import Theorems.Thm_Light_Seg_get


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchIndex
theorem _root_.solution {μ : ℕ → ℤ} {base : ℕ} (P R S J : ℕ) (raws : List ℤ)
    (words maps : List ℕ) (targets : ℕ → ℤ) (positions : ℕ → ℕ) (n : ℕ)
    (h : Seg μ base (LightTernaryWantedBatch.rows P R S J raws words maps targets positions n))
    {i : ℕ} (hi : i < (entries P R S J raws words maps targets positions n).length) :
    let e := get (entries P R S J raws words maps targets positions n) i
    μ (base+3*i) = (e.1 : ℤ) ∧ μ (base+3*i+1) = (e.2.1 : ℤ) ∧ μ (base+3*i+2) = (e.2.2 : ℤ) := by
  apply read_three _ _ hi
  rwa [cells_entries_eq_rows]
end ThreeSum.TernaryWantedBatchIndex
