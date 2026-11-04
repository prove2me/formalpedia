-- Prove2me | solution 1 for ThreeSum.TernaryParameters.projection_fiber_bits_lt_half_Hpi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:16.83685+00:00
-- url     : https://prove2.me/submissions/840d8ab5-0c71-4ffd-bb2a-0008295a7c60

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_projection_fiber_bits_lt_quarter

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    Real.log (((100000000 * m).choose (978268 * m) : ℕ) : ℝ) /
      ((100000000 * m : ℕ) * Real.log 2) < Hpi / 2 := by
  linarith [projection_fiber_bits_lt_quarter hm, Hpi_bounds.1]
end ThreeSum.TernaryParameters
