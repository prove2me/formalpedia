-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.cells_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:01:59.516749+00:00
-- url     : https://prove2.me/submissions/7d98f154-b799-444a-b46e-2e3865a8c5a7

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Theorems.Thm_ThreeSum_LightBandRawAResources_factor_bounds
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_ColorBandBounds_width_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_cells_eq
import Theorems.Thm_ThreeSum_LightBandRawAResources_count_le
import Theorems.Thm_ThreeSum_LightBandRawAResources_width_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_band_le_magnitude
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_count_le
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (n : ℕ) : cells (inputBits n + 1) n (bandSize n) ≤ envelope n :=
  by
  obtain ⟨h1, hn, hn2, _, hmn2⟩ := factor_bounds n
  have hcount := count_le n (bandSize n)
  have hcountBase := hcount.trans (Nat.mul_le_mul_left 3 hn2)
  have hwidth := width_le n (bandSize n)
  have hW : inputBits n + 1 ≤ base n := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hg := SharedReportingBankResourceBounds.band_le_magnitude n
  have hproduct : 3 * bandSize n * ColorBandBounds.count n (bandSize n) ≤ 9 * base n := by
    calc
      _ = 3 * (bandSize n * ColorBandBounds.count n (bandSize n)) := by ring
      _ ≤ 3 * (SharedReportingBankResourceBounds.magnitude n * (3 * n ^ 2)) :=
        (Nat.mul_le_mul_left 3 (Nat.mul_le_mul hg hcount))
      _ = 9 * (SharedReportingBankResourceBounds.magnitude n * n ^ 2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 9 hmn2
  rw [cells_eq]
  unfold envelope
  apply max_le <;> omega
end ThreeSum.LightBandRawAResources
