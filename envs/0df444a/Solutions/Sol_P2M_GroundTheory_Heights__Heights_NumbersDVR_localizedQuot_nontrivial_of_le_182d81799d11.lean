-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:58.511741+00:00
-- url     : https://prove2.me/submissions/df8e3605-9260-485f-8846-698bfc5b9144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtNatCastOfAddOneLe

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
universe u
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (J W : Ideal A) [W.IsPrime] (h : J ≤ W) :
    Nontrivial (LocalizedModule W.primeCompl (A ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk 1 1, 0, fun e => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at e
  obtain ⟨u, hu⟩ := e
  simp only [one_smul, smul_zero] at hu
  rw [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
    Ideal.Quotient.eq_zero_iff_mem] at hu
  exact u.2 (h hu)
end GroundTheory.Heights₂.Heights.NumbersDVR
