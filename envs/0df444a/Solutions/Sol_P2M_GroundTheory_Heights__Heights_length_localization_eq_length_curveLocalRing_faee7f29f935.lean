-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_localization_eq_length_curveLocalRing_faee7f29f935
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:27.204699+00:00
-- url     : https://prove2.me/submissions/117f22bc-ca77-4542-ba61-65fd07b8cc63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_quotient_sup_span_df8b16fd9334

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    Module.length (Localization.AtPrime (RingHom.ker (eval q)))
        (Localization.AtPrime (RingHom.ker (eval q)) ⧸ (I ⊔ Ideal.span {f}).map
          (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))) =
      Module.length (curveLocalRing I q)
        (curveLocalRing I q ⧸ Ideal.span {algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f}) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact length_quotient_sup_span _ _
end GroundTheory.Heights₂.Heights
