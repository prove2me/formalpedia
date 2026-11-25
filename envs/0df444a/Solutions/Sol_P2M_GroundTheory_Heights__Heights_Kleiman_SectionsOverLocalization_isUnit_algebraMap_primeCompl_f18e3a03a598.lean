-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_isUnit_algebraMap_primeCompl_f18e3a03a598
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:34.429887+00:00
-- url     : https://prove2.me/submissions/5f2370c7-0252-4f65-bebf-bbf362cae399

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefGenericLocalizeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeNefAboveSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefGenericLocalize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {S : Type} [CommRing S] (𝔪 : Ideal S) [𝔪.IsPrime] {K : Type} [Field K]
    [Algebra S K] (h : Function.Injective (algebraMap S K)) (y : 𝔪.primeCompl) : IsUnit (algebraMap S K y) :=
  IsUnit.mk0 _ fun h' => y.2 (by rw [(map_eq_zero_iff _ h).mp h']; exact 𝔪.zero_mem)
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
