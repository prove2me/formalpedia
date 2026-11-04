-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.setAt_subsetRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:34.048032+00:00
-- url     : https://prove2.me/submissions/87726cd9-a727-40c7-bc27-0f8c7a52e6c1

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_enumerateDownset_getD_subsetRank
import Theorems.Thm_ThreeSum_MaskDecode_decode_subsetMask


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut : ℕ} (S : Finset (Fin L)) (hS : S.card ≤ cut) :
    setAt L cut (subsetRank S) = S := by
  rw [setAt,maskAt,enumerateDownset_getD_subsetRank S hS,MaskDecode.decode_subsetMask]
end ThreeSum.SourceTableLayout
