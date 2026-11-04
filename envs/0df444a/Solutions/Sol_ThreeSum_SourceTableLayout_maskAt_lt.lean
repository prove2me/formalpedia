-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.maskAt_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:33.266744+00:00
-- url     : https://prove2.me/submissions/0403c2e2-9a05-4898-bdac-d45d46c8af90

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_maskAt_mem
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateDownset


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut i : ℕ} (hi : i < downsetCap L cut) :
    maskAt L cut i < 2^L :=
  ((mem_enumerateDownset L cut _).mp (maskAt_mem hi)).1
end ThreeSum.SourceTableLayout
