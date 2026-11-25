-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:38.439316+00:00
-- url     : https://prove2.me/submissions/d6fd90df-52bf-490a-911e-3d18584dd2ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332


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
theorem _root_.solution (P : Ideal (MRing ι R)) (u : J → MRing ι R) (p : MRing ι R) :
    liftForm p ∈ blowUpOf P u ↔ p ∈ P := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.NumbersDVR
