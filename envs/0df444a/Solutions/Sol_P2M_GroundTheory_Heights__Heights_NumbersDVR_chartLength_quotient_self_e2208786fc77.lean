-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_quotient_self_e2208786fc77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:11.139839+00:00
-- url     : https://prove2.me/submissions/043e9045-78ef-4fbf-b8f5-986c50f788df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {A : Type*} [CommRing A] (I : Ideal A) :
    Module.length A (A ⧸ I) = Module.length (A ⧸ I) (A ⧸ I) :=
  Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
end GroundTheory.Heights₂.Heights.NumbersDVR
