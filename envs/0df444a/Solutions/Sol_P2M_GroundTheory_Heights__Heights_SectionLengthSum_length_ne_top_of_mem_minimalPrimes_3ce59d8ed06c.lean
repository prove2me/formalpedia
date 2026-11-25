-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionLengthSum_length_ne_top_of_mem_minimalPrimes_3ce59d8ed06c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:38.55482+00:00
-- url     : https://prove2.me/submissions/08bac1ad-c305-4ba2-9a52-5b23adade87c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionLengthSum

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
open GroundTheory.Heights₂.Heights.SectionLengthSum
namespace GroundTheory.Heights₂.Heights.SectionLengthSum
theorem _root_.solution {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top
end GroundTheory.Heights₂.Heights.SectionLengthSum
