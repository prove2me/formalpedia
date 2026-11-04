-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.time_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:07:51.277791+00:00
-- url     : https://prove2.me/submissions/74c508e6-4c16-4ef1-b954-e9c496ef8730

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_time_eq
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
import Definitions.Def_WeightedCache3SUM_Alias_081c2d9f896753a1
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution {nA nB nC n : ℕ} (k : ℕ) (hn : 0 < n)
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.time (maxMod n) nA nB nC (bandSize n) (radix n) (primeWindow n) (n^k) ≤
      BandPrimeCosts.timeBudget k n+1160 := by
  rw [time_eq]
  exact Nat.add_le_add_right (BandPrimeCosts.setup_time_le_budget k hn (count_le ha hb hc)) 1160
end ThreeSum.EncodedColorPrimeCosts
