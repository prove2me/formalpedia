-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:37.551253+00:00
-- url     : https://prove2.me/submissions/49b0ed02-0ee9-46c7-9f6d-26ed3793d483

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters

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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← hI, Ideal.map_sup,
    Ideal.map_span, ← Set.range_comp, Ideal.map_quotient_self, sup_bot_eq]
  rfl
end GroundTheory.Heights₂.Heights
