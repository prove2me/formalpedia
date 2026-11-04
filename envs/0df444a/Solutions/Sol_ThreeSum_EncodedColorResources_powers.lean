-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:52:15.330228+00:00
-- url     : https://prove2.me/submissions/87ce2def-89e6-4a8a-9c96-62f2e87e67c6

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac
import Theorems.Thm_ThreeSum_SourceBandFinite_occurrence
import Theorems.Thm_ThreeSum_SourceFiniteData_Stored_occurrence


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)
end ThreeSum.EncodedColorResources
