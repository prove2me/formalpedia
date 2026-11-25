-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalisationModelLocalization_toFrac_mem_05a26a7b558e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:56.860117+00:00
-- url     : https://prove2.me/submissions/94b2950b-9dcb-43d2-9f07-ef0685d06bc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalisationModelLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PNormalisationModelLocalizationX

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
namespace GroundTheory.Heights₂.Heights.NormalisationModelLocalization
theorem _root_.solution (f : MvPolynomial (Fin n) ℂ) :
    toFrac J q f ∈ integralClosure (curveLocalRing J q) (FractionRing (curveLocalRing J q)) :=
  Subalgebra.algebraMap_mem _ _
end GroundTheory.Heights₂.Heights.NormalisationModelLocalization
