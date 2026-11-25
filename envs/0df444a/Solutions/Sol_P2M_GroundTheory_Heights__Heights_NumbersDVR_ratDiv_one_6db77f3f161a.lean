-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:34.390446+00:00
-- url     : https://prove2.me/submissions/1cc9a654-87a6-47a7-9a7b-a10fd8655890

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_one_e110294ad3db


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
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by
  funext W
  rw [ratDiv, divCycle_one, sub_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR
