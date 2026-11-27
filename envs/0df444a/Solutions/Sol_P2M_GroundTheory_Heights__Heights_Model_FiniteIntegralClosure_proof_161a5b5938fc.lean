-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_proof_161a5b5938fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:56.256969+00:00
-- url     : https://prove2.me/submissions/696cf2cf-69b1-4bfe-b1e4-99fe0160face

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFiniteIntegralClosure
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charZero_6b5f227e7c28


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
namespace FiniteIntegralClosure
theorem _root_.solution : FiniteIntegralClosure.Statement := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists A
  rcases CharP.char_is_prime_or_zero A p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_of_charP p A K L
  · have : CharZero A := CharP.charP_to_charZero A
    exact finite_integralClosure_of_charZero A K L
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.Model
