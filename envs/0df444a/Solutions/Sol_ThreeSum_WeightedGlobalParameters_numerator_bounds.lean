-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.numerator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:56.199488+00:00
-- url     : https://prove2.me/submissions/20a7015e-8c96-44cf-8f4a-9a9b696cb073

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCacheParameters_An_bounds
import Theorems.Thm_WeightedCacheParameters_Bn_bounds
import Theorems.Thm_WeightedCacheParameters_Gn_bounds
import Theorems.Thm_WeightedCacheParameters_Hn_bounds
import Theorems.Thm_WeightedCacheParameters_Qn_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    2*WeightedCacheParameters.Bn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn+2*WeightedCacheParameters.Qn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.An<certificateExponent*WeightedCacheParameters.Hn ∧
    WeightedCacheParameters.Hn+WeightedCacheParameters.Gn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn<certificateExponent*WeightedCacheParameters.Hn := by
  obtain ⟨hH0,hH1⟩ := WeightedCacheParameters.Hn_bounds
  obtain ⟨hA0,hA1⟩ := WeightedCacheParameters.An_bounds
  obtain ⟨hG0,hG1⟩ := WeightedCacheParameters.Gn_bounds
  obtain ⟨hB0,hB1⟩ := WeightedCacheParameters.Bn_bounds
  obtain ⟨hQ0,hQ1⟩ := WeightedCacheParameters.Qn_bounds
  norm_num [certificateExponent] at *
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
end ThreeSum.WeightedGlobalParameters
