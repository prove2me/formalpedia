-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.enumerateDownset_getD_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:37.170813+00:00
-- url     : https://prove2.me/submissions/53eca0f0-2d7e-47c2-b9f2-f70279653cb7

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_enumerateThrough_getD_rank
import Theorems.Thm_ThreeSum_SubsetAddress_weight_le_width


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut m : ℕ}
    (hm : m < 2^L) (hk : weight L m ≤ cut) (fallback : ℕ) :
    (enumerateDownset L cut).getD (downsetRank L m) fallback = m := by
  exact enumerateThrough_getD_rank ⟨hm,rfl⟩ (le_min hk (weight_le_width hm)) fallback
end ThreeSum.SourceTableLayout
