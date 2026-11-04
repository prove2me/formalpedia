-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.output_log_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:53.606212+00:00
-- url     : https://prove2.me/submissions/6e0e5e02-a358-47d3-a449-8c118b06725f

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) : 0 < Real.log (outputSize m : ℝ) :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 1 < (16 : ℕ)) (outputSize_ge_sixteen hm))
end ThreeSum.TernaryPrincipalDimensions
