-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:41:54.441495+00:00
-- url     : https://prove2.me/submissions/88b24d8f-46ef-4fd3-887e-61c84b91d368

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivisorIdealCycle

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))
end GroundTheory.Heights₂.Heights.NumbersDVR
