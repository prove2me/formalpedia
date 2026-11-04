-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.output_log_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:55:36.487191+00:00
-- url     : https://prove2.me/submissions/e4b8bcac-a57b-45f7-835a-51d836d3ff6f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) : 0 < Real.log (outputSize m : ℝ) :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 1 < (16 : ℕ)) (outputSize_ge_sixteen hm))
end ThreeSum.WeightedGlobalPrincipalDimensions
