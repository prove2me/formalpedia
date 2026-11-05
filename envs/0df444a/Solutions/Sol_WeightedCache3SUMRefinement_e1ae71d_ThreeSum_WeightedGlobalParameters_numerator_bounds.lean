-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.numerator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:12:18.253729+00:00
-- url     : https://prove2.me/submissions/0e9eaeb8-2e66-49f2-8c6c-9424e75ec195

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCacheParameters_e1ae71d_An_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Bn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Gn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Qn_bounds


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    2*WeightedCacheParameters_e1ae71d.Bn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn+2*WeightedCacheParameters_e1ae71d.Qn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.An<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    WeightedCacheParameters_e1ae71d.Hn+WeightedCacheParameters_e1ae71d.Gn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn := by
  obtain ⟨hH0,hH1⟩ := WeightedCacheParameters_e1ae71d.Hn_bounds
  obtain ⟨hA0,hA1⟩ := WeightedCacheParameters_e1ae71d.An_bounds
  obtain ⟨hG0,hG1⟩ := WeightedCacheParameters_e1ae71d.Gn_bounds
  obtain ⟨hB0,hB1⟩ := WeightedCacheParameters_e1ae71d.Bn_bounds
  obtain ⟨hQ0,hQ1⟩ := WeightedCacheParameters_e1ae71d.Qn_bounds
  norm_num [certificateExponent] at *
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
