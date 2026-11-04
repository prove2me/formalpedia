-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:54:16.716671+00:00
-- url     : https://prove2.me/submissions/42c36079-b00e-4793-8df9-a2a276d5c501

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Definitions.Def_WeightedCache3SUM_Alias_32619216de5760ac
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_downset_le_pow
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_overhead_bound
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_eq
import Theorems.Thm_ThreeSum_SourceBandFinite_occurrence
import Theorems.Thm_ThreeSum_SourceControlLayout_span_eq


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) :
    SourceBandBankLayout.span (half n) (blocks n) (2*half n*blocks n) ≤ 100*(magnitude n+1)^3 := by
  have H := components n
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hJ := H.blocksBound
  have hS := H.occurrence
  have hP := H.prime
  have hPP := H.primePower
  have hM := H.positive
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hcap := (downset_le_pow (width (half n) (blocks n)) (2*half n*blocks n)).trans hpower
  have hlogP : Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show 512*half n ≤ magnitude n by omega) hP
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hlogE : Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show width (half n) (blocks n) ≤ magnitude n by omega) hPP
    unfold LightBlockSourceBuild.endpointBound
    change Nat.log 2 (width (half n) (blocks n)*
      (LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n))+1) ≤ _
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hscratch := SourceBandBanksCosts.overhead_bound (half n) (blocks n)
  change LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤
    blocks n+2*width (half n) (blocks n)+(width (half n) (blocks n)+1)^2+
    Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1)+
    Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+20 at hscratch
  have hquad := Nat.pow_le_pow_left hW 2
  have hwork : LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ 30*(magnitude n+1)^2 := by
    nlinarith
  have hstride : LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2 ≤
      12*(magnitude n+1)^2 := by
    have hfamily := Nat.mul_le_mul hW hcap
    unfold LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
    nlinarith
  have hprod := Nat.mul_le_mul hS hstride
  rw [SourceBandBanksCosts.span_eq]
  change LightBlockSourceCatalog.count (half n) (blocks n)*
    (LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2)+
    downsetCap (width (half n) (blocks n)) (2*half n*blocks n)+width (half n) (blocks n)+2+
    LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ _
  nlinarith
end ThreeSum.SharedReportingBankResourceBounds
