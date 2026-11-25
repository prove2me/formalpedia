-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:26.070814+00:00
-- url     : https://prove2.me/submissions/9b44717d-b38a-4abc-98a1-235bfe25f5a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLoc

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
open MvPolynomial HomLocLaurent
noncomputable section
universe u
set_option linter.style.haveILetI false
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    (h : Function.Surjective (algebraMap S C)) (I : Ideal C) :
    Module.length S (C ⧸ I) = Module.length C (C ⧸ I) :=
  Module.length_eq_of_surjective h
end GroundTheory.Heights₂.Heights.NumbersDVR
