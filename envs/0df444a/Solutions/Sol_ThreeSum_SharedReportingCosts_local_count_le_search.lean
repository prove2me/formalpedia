-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.local_count_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:32.629121+00:00
-- url     : https://prove2.me/submissions/88b5d978-b618-44f8-b51c-ee9142ed9fb0

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
namespace ThreeSum.SharedReportingCosts
theorem _root_.solution (n : ℕ) : localCount n ≤ localSearch 257 n := by
  have hsize : 2*half n=muZero n := rfl
  unfold localCount LightReportingPrefixArrays.localCount localWidth
  calc
    _ ≤ 2^(512*half n)*2^(2*half n) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ = 2^(257*(2*half n)) := by rw [← pow_add]; congr 1; ring
    _ = 2^(257*muZero n) := by rw [hsize]
    _ ≤ localSearch 257 n :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 257 (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _))
end ThreeSum.SharedReportingCosts
