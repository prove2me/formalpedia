-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:49.459091+00:00
-- url     : https://prove2.me/submissions/8a1b0927-b737-4660-bed8-eab898252201

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem

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
theorem _root_.solution {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) (u : J → MRing ι R) (p : MRing ι R) :
    aeval (blowUpSubst P u) (liftForm p) = Polynomial.C (Ideal.Quotient.mk P p) := by
  have e : (aeval (blowUpSubst P u)).comp (liftForm : MRing ι R →ₐ[R] MRing (extIdx ι J) R) =
      (Polynomial.CAlgHom).comp (Ideal.Quotient.mkₐ R P) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, blowUpSubst]
  exact DFunLike.congr_fun e p
end GroundTheory.Heights₂.Heights.NumbersDVR
