-- Prove2me | solution 1 for ThreeSum.LightSourceFlagArray.flag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:56:53.797601+00:00
-- url     : https://prove2.me/submissions/634acb77-fbd6-43b7-a215-5c12d879c0af

import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Theorems.Thm_ThreeSum_LightSourceTrim_rowFlag_le
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagArray
open Light SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
namespace ThreeSum.LightSourceFlagArray
theorem _root_.solution (J L h p cap : ℕ) (sel candidate : ℕ → ℕ)
    (w0 w1 counts : ℕ → ℕ → ℕ) (mask : ℕ) :
    flag J L h p cap sel candidate w0 w1 counts mask ≤ 1 :=
  product_le _ (fun _ _ => LightSourceTrim.rowFlag_le ..) le_rfl
end ThreeSum.LightSourceFlagArray
