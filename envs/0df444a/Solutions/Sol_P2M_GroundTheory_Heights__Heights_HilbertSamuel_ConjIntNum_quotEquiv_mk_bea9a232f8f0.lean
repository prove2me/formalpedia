-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_mk_bea9a232f8f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:41.251704+00:00
-- url     : https://prove2.me/submissions/71de006f-59fe-400d-bd7e-a2490316653a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
theorem _root_.solution (τ : F ≃+* F) (J : Ideal (MRing ι F)) (f : MRing ι F) :
    quotEquiv τ J (Ideal.Quotient.mk J f) = Ideal.Quotient.mk _ (MvPolynomial.map (τ : F →+* F) f) :=
  rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
