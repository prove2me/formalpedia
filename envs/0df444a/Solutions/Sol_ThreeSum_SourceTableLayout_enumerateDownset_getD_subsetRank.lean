-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.enumerateDownset_getD_subsetRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:58.987771+00:00
-- url     : https://prove2.me/submissions/d5f20ac5-ca66-45cb-8016-6970fc86a7ad

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_enumerateDownset_getD_rank
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut : ℕ} (S : Finset (Fin L))
    (hS : S.card ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (subsetRank S) fallback = subsetMask S := by
  have hmask := subsetMask_isMask S
  exact enumerateDownset_getD_rank hmask.1 (hmask.2.trans_le hS) fallback
end ThreeSum.SourceTableLayout
