-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.ledger_individual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:45.179233+00:00
-- url     : https://prove2.me/submissions/2a82dbe3-288c-4fdb-af8d-cfbb114f536b

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_numerator_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_Hn_pos
import Theorems.Thm_WeightedCacheParameters_numerator_bounds


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    2*bankEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi+2*queryEntropy/Hpi<certificateExponent ∧
    2*Halpha/Hpi<certificateExponent ∧
    1+partitionEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi<certificateExponent := by
  obtain ⟨hB,hQ,hA,hP,hI⟩ := numerator_bounds
  have hH := WeightedCacheParameters.Hn_pos
  have hHne := hH.ne'
  have htwo := log_two_pos.ne'
  have hB' := (div_lt_iff₀ hH).mpr hB
  have hQ' := (div_lt_iff₀ hH).mpr hQ
  have hA' := (div_lt_iff₀ hH).mpr hA
  have hP' := (div_lt_iff₀ hH).mpr hP
  have hI' := (div_lt_iff₀ hH).mpr hI
  have he :
      2*bankEntropy/Hpi=2*WeightedCacheParameters.Bn/WeightedCacheParameters.Hn ∧
      2-partitionEntropy/Hpi+2*queryEntropy/Hpi=(2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn+2*WeightedCacheParameters.Qn)/WeightedCacheParameters.Hn ∧
      2*Halpha/Hpi=2*WeightedCacheParameters.An/WeightedCacheParameters.Hn ∧
      1+partitionEntropy/Hpi=(WeightedCacheParameters.Hn+WeightedCacheParameters.Gn)/WeightedCacheParameters.Hn ∧
      2-partitionEntropy/Hpi=(2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn)/WeightedCacheParameters.Hn := by
    unfold Hpi Halpha partitionEntropy bankEntropy queryEntropy
    refine ⟨?_,?_,?_,?_,?_⟩ <;> field_simp
  exact ⟨he.1 ▸ hB',he.2.1 ▸ hQ',he.2.2.1 ▸ hA',he.2.2.2.1 ▸ hP',he.2.2.2.2 ▸ hI'⟩
end ThreeSum.WeightedGlobalParameters
