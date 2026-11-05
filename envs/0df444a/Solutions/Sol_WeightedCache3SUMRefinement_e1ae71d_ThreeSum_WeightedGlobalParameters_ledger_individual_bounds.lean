-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.ledger_individual_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:13:17.612233+00:00
-- url     : https://prove2.me/submissions/abf4a072-558e-46c7-847c-5411c5d7e08c

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_numerator_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_pos
import Theorems.Thm_WeightedCacheParameters_e1ae71d_numerator_bounds


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    2*bankEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi+2*queryEntropy/Hpi<certificateExponent ∧
    2*Halpha/Hpi<certificateExponent ∧
    1+partitionEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi<certificateExponent := by
  obtain ⟨hB,hQ,hA,hP,hI⟩ := numerator_bounds
  have hH := WeightedCacheParameters_e1ae71d.Hn_pos
  have hHne := hH.ne'
  have htwo := log_two_pos.ne'
  have hB' := (div_lt_iff₀ hH).mpr hB
  have hQ' := (div_lt_iff₀ hH).mpr hQ
  have hA' := (div_lt_iff₀ hH).mpr hA
  have hP' := (div_lt_iff₀ hH).mpr hP
  have hI' := (div_lt_iff₀ hH).mpr hI
  have he :
      2*bankEntropy/Hpi=2*WeightedCacheParameters_e1ae71d.Bn/WeightedCacheParameters_e1ae71d.Hn ∧
      2-partitionEntropy/Hpi+2*queryEntropy/Hpi=(2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn+2*WeightedCacheParameters_e1ae71d.Qn)/WeightedCacheParameters_e1ae71d.Hn ∧
      2*Halpha/Hpi=2*WeightedCacheParameters_e1ae71d.An/WeightedCacheParameters_e1ae71d.Hn ∧
      1+partitionEntropy/Hpi=(WeightedCacheParameters_e1ae71d.Hn+WeightedCacheParameters_e1ae71d.Gn)/WeightedCacheParameters_e1ae71d.Hn ∧
      2-partitionEntropy/Hpi=(2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn)/WeightedCacheParameters_e1ae71d.Hn := by
    unfold Hpi Halpha partitionEntropy bankEntropy queryEntropy
    refine ⟨?_,?_,?_,?_,?_⟩ <;> field_simp
  exact ⟨he.1 ▸ hB',he.2.1 ▸ hQ',he.2.2.1 ▸ hA',he.2.2.2.1 ▸ hP',he.2.2.2.2 ▸ hI'⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
