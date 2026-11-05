-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.analytic_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:11:18.765804+00:00
-- url     : https://prove2.me/submissions/6bf4ac1c-f253-46d7-9691-bff24e51baf6

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_bounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Halpha_bounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_partitionEntropy_bounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_bankEntropy_bounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_queryEntropy_bounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
