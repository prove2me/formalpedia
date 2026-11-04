-- Prove2me | solution 1 for ThreeSum.LightTernaryMetadata.writeRecord_current
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:42.966308+00:00
-- url     : https://prove2.me/submissions/e01be577-8c2b-4d63-b49f-c8abda58846d

import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryMetadata
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMetadata
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryMetadata
theorem _root_.solution {μ : ℕ → ℤ} {base n j W low high m : ℕ} (hj : j < n) :
    RecordAt (writeRecord μ base n j (LightTernaryCodes.digit W low high m)
      (LightTernaryCodes.zeroCode W low high m) (LightTernaryCodes.oneCode W high m) m)
      base n j W low high m := by
  unfold RecordAt writeRecord
  simp only [Function.update_self, Function.update_of_ne (by omega :
      base+j ≠ base+3*n+j), Function.update_of_ne (by omega :
      base+j ≠ base+2*n+j), Function.update_of_ne (by omega :
      base+j ≠ base+n+j), Function.update_of_ne (by omega :
      base+n+j ≠ base+3*n+j), Function.update_of_ne (by omega :
      base+n+j ≠ base+2*n+j), Function.update_of_ne (by omega :
      base+2*n+j ≠ base+3*n+j), and_self]
end ThreeSum.LightTernaryMetadata
