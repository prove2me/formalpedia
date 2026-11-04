-- Prove2me | solution 1 for ThreeSum.LightZetaPass.choose_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:55:01.889187+00:00
-- url     : https://prove2.me/submissions/34f1099f-233c-402f-bca3-54ad19920507

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ


set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaPass
theorem _root_.solution {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    L.choose j ≤ downsetCap L cut := by
  have ho := layerOffset_mono L (show j+1 ≤ min cut L+1 by omega)
  rw [layerOffset_succ] at ho
  unfold downsetCap
  omega
end ThreeSum.LightZetaPass
