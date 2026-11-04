-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.total_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:13.136318+00:00
-- url     : https://prove2.me/submissions/5f402068-15fe-46b8-9f8e-fb4afb2f273d

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
namespace ThreeSum.SharedReportingBankCosts
theorem _root_.solution {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n) ≤
      3*bandCount n^2*TrimScales.scheduleCount n := by
  have hb := SourceBandCosts.size_le_bandCount hB
  have hc := SourceBandCosts.size_le_bandCount hC
  unfold SharedReportingBankRows.total SharedReportingBankRows.pairs
  rw [show LightBlockSourceCatalog.count (half n) (blocks n)=TrimScales.scheduleCount n from
    BlockSourceCatalogCosts.count_eq_scheduleCount n]
  calc
    _ ≤ TrimScales.scheduleCount n*bandCount n*bandCount n :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hc
    _ = bandCount n^2*TrimScales.scheduleCount n := by ring
    _ ≤ 3*bandCount n^2*TrimScales.scheduleCount n := by nlinarith
end ThreeSum.SharedReportingBankCosts
