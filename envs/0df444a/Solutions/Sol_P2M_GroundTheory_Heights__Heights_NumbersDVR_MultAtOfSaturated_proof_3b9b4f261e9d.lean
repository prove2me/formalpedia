-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtOfSaturated_proof_3b9b4f261e9d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:06:32.359832+00:00
-- url     : https://prove2.me/submissions/4f91f0f6-8871-4d9b-b581-4bcca24f4b25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtOfSaturated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_map_bijective_of_saturated_276e2f64ac24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_isSimpleModule_99b39ffeb975


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace MultAtOfSaturated
theorem _root_.solution : MultAtOfSaturated.Statement.{u} := by
  intro R _ K ι J Q _ hJQ hsat
  refine ⟨mem_minimalPrimes_of_saturated J Q hJQ hsat, ?_⟩
  unfold multAt
  rw [(LinearEquiv.ofBijective _ (localizedQuot_map_bijective_of_saturated J Q hJQ hsat)).length_eq,
    Module.length_eq_one_iff]
  exact localizedQuotient_isSimpleModule Q
end MultAtOfSaturated
end GroundTheory.Heights₂.Heights.NumbersDVR
