-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleFiniteSupport_proof_010201f3d63e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:36.838595+00:00
-- url     : https://prove2.me/submissions/28ad181b-b713-43f1-a57c-27ab7dae44a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport

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
namespace DivCycleFiniteSupport
theorem _root_.solution : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dif_neg]
  exact fun h => hmin h.1
end DivCycleFiniteSupport
end GroundTheory.Heights₂.Heights.NumbersDVR
