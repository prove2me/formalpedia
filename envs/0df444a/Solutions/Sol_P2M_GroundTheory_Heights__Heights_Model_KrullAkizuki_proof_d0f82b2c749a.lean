-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_proof_d0f82b2c749a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:40.200455+00:00
-- url     : https://prove2.me/submissions/53492a1d-eb16-407c-a87c-67f1f970e45f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_noetherian_and_dimensionLEOne_e457c86826f4

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
open GroundTheory.Heights₂.Heights.Model.KrullAkizuki
namespace GroundTheory.Heights₂.Heights.Model.KrullAkizuki
theorem _root_.solution (h : KrullAkizukiQuotientLength.Statement) : KrullAkizuki.Statement := by
  refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => ?_, fun R _ _ _ hR K _ _ _ => ?_⟩
  · obtain ⟨h₁, h₂⟩ := noetherian_and_dimensionLEOne (K := K) S (h R hR K L S)
    refine ⟨h₁, ?_⟩
    have := (Ring.krullDimLE_iff (R := S) (n := 1)).mp inferInstance
    exact_mod_cast this
  · obtain ⟨h₁, h₂⟩ :=
      noetherian_and_dimensionLEOne (K := K) (L := K) (integralClosure R K) (h R hR K K _)
    have : IsIntegrallyClosed (integralClosure R K) :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K (L := K)
    exact { }
end GroundTheory.Heights₂.Heights.Model.KrullAkizuki
