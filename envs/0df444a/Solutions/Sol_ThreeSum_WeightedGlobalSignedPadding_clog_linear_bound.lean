-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPadding.clog_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:16:53.546328+00:00
-- url     : https://prove2.me/submissions/63a5baf4-e37c-4b8e-9f29-f786aef09253

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_clog_power_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedPadding
theorem _root_.solution {b x : ℕ} (hb : 1<b) (hx : 0<x) :
    (Nat.clog b x : ℝ) ≤ 1+Real.log (x : ℝ)/Real.log (b : ℝ) := by
  have hbR : (1 : ℝ)<b := by exact_mod_cast hb
  have hbp : (0 : ℝ)<b := by linarith
  have hxp : (0 : ℝ)<x := by exact_mod_cast hx
  have hh : (b : ℝ)^(Nat.clog b x) ≤ (b : ℝ)*(x : ℝ) := by
    exact_mod_cast clog_power_bound hb hx
  have hl := Real.log_le_log (pow_pos hbp _) hh
  rw [Real.log_pow,Real.log_mul hbp.ne' hxp.ne'] at hl
  calc
    _ ≤ (Real.log (b : ℝ)+Real.log (x : ℝ))/Real.log (b : ℝ) :=
      (le_div_iff₀ (Real.log_pos hbR)).mpr hl
    _ = _ := by rw [add_div,div_self (Real.log_pos hbR).ne']
end ThreeSum.WeightedGlobalSignedPadding
