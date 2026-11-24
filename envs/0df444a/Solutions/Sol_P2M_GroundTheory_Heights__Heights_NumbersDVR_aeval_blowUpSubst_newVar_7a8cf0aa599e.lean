-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:38.436791+00:00
-- url     : https://prove2.me/submissions/54195033-e382-487e-927f-5cddc105bee8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart

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
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (P : Ideal (MRing ι R)) (u : J → MRing ι R) (k : J) :
    aeval (blowUpSubst P u) (newVar k : MRing (extIdx ι J) R) = Polynomial.C (Ideal.Quotient.mk P (u k)) * Polynomial.X := by
  simp [newVar, blowUpSubst]
end GroundTheory.Heights₂.Heights.NumbersDVR
