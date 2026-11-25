-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_eventualValue_zero_2601218ff46a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:08.503034+00:00
-- url     : https://prove2.me/submissions/c78fd578-c98a-4fe4-bf41-900efbab595e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero

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
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} : eventualValue (0 : (K → ℤ) → ℤ) = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, hm⟩ := hc.choose_spec.exists
    exact hm.symm
  · rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
