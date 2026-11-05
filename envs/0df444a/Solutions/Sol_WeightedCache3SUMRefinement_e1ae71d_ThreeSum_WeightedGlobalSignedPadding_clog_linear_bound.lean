-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding.clog_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:25:15.090169+00:00
-- url     : https://prove2.me/submissions/10ff13d6-7322-49fc-ab83-98781e92409e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedPadding_clog_power_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedPadding
