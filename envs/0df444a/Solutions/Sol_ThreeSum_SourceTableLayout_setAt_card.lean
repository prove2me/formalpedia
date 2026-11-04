-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.setAt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:15:58.554953+00:00
-- url     : https://prove2.me/submissions/2035e065-7878-4b4d-91ef-d1a63fd34d8a

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_mem
import Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_lt
import Theorems.Thm_ThreeSum_MaskDecode_decode_card
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateDownset


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut i : ℕ} (hi : i < downsetCap L cut) :
    (setAt L cut i).card ≤ cut := by
  rw [setAt,MaskDecode.decode_card (maskAt_lt hi)]
  exact ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).2
end ThreeSum.SourceTableLayout
