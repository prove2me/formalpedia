-- Prove2me | solution 1 for ThreeSum.TernaryParameters.analytic_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:04.828199+00:00
-- url     : https://prove2.me/submissions/3c58666c-58c4-4e19-b6a8-44c7d41b686e

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_Halpha_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_partitionEntropy_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_bankEntropy_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_queryEntropy_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution :
    0 < bankEntropy ∧ 0 < queryEntropy ∧ partitionEntropy < Hpi ∧
    Halpha < bankEntropy ∧ (Hpi + partitionEntropy) / 2 < Halpha ∧
    0 < Hpi - partitionEntropy + 2 * queryEntropy := by
  obtain ⟨hH0, hH1⟩ := Hpi_bounds
  obtain ⟨hA0, hA1⟩ := Halpha_bounds
  obtain ⟨hG0, hG1⟩ := partitionEntropy_bounds
  obtain ⟨hB0, hB1⟩ := bankEntropy_bounds
  obtain ⟨hQ0, hQ1⟩ := queryEntropy_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
end ThreeSum.TernaryParameters
