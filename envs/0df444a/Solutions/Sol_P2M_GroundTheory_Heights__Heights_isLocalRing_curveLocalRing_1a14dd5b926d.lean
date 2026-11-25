-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:48.666263+00:00
-- url     : https://prove2.me/submissions/cbe1079a-b367-4bc0-9826-39e9fb5566f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdFiniteNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdFiniteNonZeroDivisor

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    [Nontrivial (curveLocalRing I q)] : IsLocalRing (curveLocalRing I q) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))))) Ideal.Quotient.mk_surjective
end GroundTheory.Heights₂.Heights
