-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.dimensions_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:02:01.947814+00:00
-- url     : https://prove2.me/submissions/5ad093fb-7fb6-4759-a34b-c1d1bba3485f

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_BlockSourceSharing_cutoff_eq
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_band_le_magnitude
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : width n+1 ≤ scale n ∧ blocks n+1 ≤ scale n ∧
    mu n+1 ≤ scale n ∧ bandSize n ≤ scale n ∧ radix n ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  have hw : width n+1 ≤ scale n := H.widthBound.trans hm
  have hj : blocks n+1 ≤ scale n := H.blocksBound.trans hm
  have ht := H.switchBase.trans hm
  rw [show 2*SharedReportingBankResourceBounds.half n*SharedReportingBankResourceBounds.blocks n=mu n from
    BlockSourceSharing.cutoff_eq n] at ht
  have hg := (SharedReportingBankResourceBounds.band_le_magnitude n).trans hm
  have hy := primeWindow_ge_two n
  have hr : radix n ≤ maxMod n := by
    unfold maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨hw,hj,by omega,hg,hr.trans (scale_bounds n).2.2.2.2.1⟩
end ThreeSum.EncodedColorResources
