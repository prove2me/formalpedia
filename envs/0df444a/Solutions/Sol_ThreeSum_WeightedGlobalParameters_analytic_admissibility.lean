-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.analytic_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:23.450232+00:00
-- url     : https://prove2.me/submissions/3dc2514a-28f0-4ba5-bdf8-3d56fa46219c

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Halpha_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_partitionEntropy_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_bankEntropy_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_queryEntropy_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
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
end ThreeSum.WeightedGlobalParameters
