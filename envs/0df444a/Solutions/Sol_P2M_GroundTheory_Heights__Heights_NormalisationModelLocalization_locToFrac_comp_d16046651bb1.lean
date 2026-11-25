-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_comp_d16046651bb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:13.337189+00:00
-- url     : https://prove2.me/submissions/c1bd4110-7cb6-4332-bd01-060939b633ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_locToFrac_algebraMap_e1ab69daa521

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalisationModelLocalization
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
variable (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
variable {M}
variable (M)
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (hJ : J.IsPrime) (hq : q ∈ zeroSet J) :
    (locToFrac M hJ hq).comp (locToModel M) = algebraMap (curveLocalRing J q) (FractionRing (curveLocalRing J q)) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl
  refine RingHom.ext fun f => ?_
  change locToFrac M hJ hq (polyLocToModel M (algebraMap _ _ f)) = toFrac J q f
  rw [polyLocToModel_algebraMap, locToFrac_algebraMap, modelToFrac_mk, toFracModel_rename]
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
