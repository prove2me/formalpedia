-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_localizedModule_self_754de89026ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:13.905638+00:00
-- url     : https://prove2.me/submissions/0a77e6f7-db79-4592-95a5-fa29371e3284

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutLocalizedModule
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalizedQuotLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedQuotient

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
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] (P : Ideal B) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl B) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) :=
  ((IsLocalizedModule.iso P.primeCompl (Algebra.linearMap B (Localization.AtPrime P))).extendScalarsOfIsLocalization
    P.primeCompl (Localization.AtPrime P)).length_eq
end GroundTheory.Heights₂.Heights
