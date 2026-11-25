-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:45.111053+00:00
-- url     : https://prove2.me/submissions/fe42d6af-b3fa-479c-8b50-5df6ec9e0e86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_subsingleton_of_not_le_8af77c4e3823
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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace MultAtPrimeAtMinimal
theorem _root_.solution : MultAtPrimeAtMinimal.Statement := by
  intro R _ K ι J Q W _ _ hJQ hW
  unfold multAt
  by_cases hQW : Q ≤ W
  · have hEq : Q = W := le_antisymm hQW (hW.2 ⟨‹Q.IsPrime›, hJQ⟩ hQW)
    subst hEq
    rw [if_pos rfl, Module.length_eq_one_iff]
    exact localizedQuotient_isSimpleModule Q
  · have hne : Q ≠ W := fun h => hQW h.le
    rw [if_neg hne, Module.length_eq_zero_iff]
    exact localizedQuotient_subsingleton_of_not_le Q W hQW
end MultAtPrimeAtMinimal
end GroundTheory.Heights₂.Heights.NumbersDVR
