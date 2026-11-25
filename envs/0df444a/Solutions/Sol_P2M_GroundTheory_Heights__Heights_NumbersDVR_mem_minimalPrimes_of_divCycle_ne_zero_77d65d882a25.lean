-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:55.647097+00:00
-- url     : https://prove2.me/submissions/dee8400c-ab9d-42fc-8823-9202a80ce055

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
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.NumbersDVR
