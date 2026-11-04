-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.subsetMask_setAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:34.257206+00:00
-- url     : https://prove2.me/submissions/abd9bc22-18c2-4a7f-971d-bf5144e3611c

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_lt
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut i : ℕ} (hi : i < downsetCap L cut) :
    subsetMask (setAt L cut i) = maskAt L cut i :=
  MaskDecode.subsetMask_decode (maskAt_lt hi)
end ThreeSum.SourceTableLayout
