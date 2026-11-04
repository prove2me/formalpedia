-- Prove2me | solution 1 for ThreeSum.TernaryParameters.ledger_individual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:14.398123+00:00
-- url     : https://prove2.me/submissions/0a4ce3e9-bdf7-4a82-b653-d58f20f98dee

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
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution :
    2 * bankEntropy / Hpi < certificateExponent ∧
    2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi < certificateExponent ∧
    2 * Halpha / Hpi < certificateExponent ∧
    1 + partitionEntropy / Hpi < certificateExponent ∧
    2 - partitionEntropy / Hpi < certificateExponent := by
  obtain ⟨hH0, hH1⟩ := Hpi_bounds
  obtain ⟨hA0, hA1⟩ := Halpha_bounds
  obtain ⟨hG0, hG1⟩ := partitionEntropy_bounds
  obtain ⟨hB0, hB1⟩ := bankEntropy_bounds
  obtain ⟨hQ0, hQ1⟩ := queryEntropy_bounds
  have hn : Hpi ≠ 0 := ne_of_gt Hpi_pos
  have hquery : 2 - partitionEntropy / Hpi + 2 * queryEntropy / Hpi =
      (2 * Hpi - partitionEntropy + 2 * queryEntropy) / Hpi := by
    field_simp [hn]
  have hhist : 1 + partitionEntropy / Hpi = (Hpi + partitionEntropy) / Hpi := by
    field_simp [hn]
  have hinc : 2 - partitionEntropy / Hpi = (2 * Hpi - partitionEntropy) / Hpi := by
    field_simp [hn]
  rw [hquery, hhist, hinc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    apply (div_lt_iff₀ Hpi_pos).2 <;>
    norm_num [certificateExponent] at * <;> linarith
end ThreeSum.TernaryParameters
