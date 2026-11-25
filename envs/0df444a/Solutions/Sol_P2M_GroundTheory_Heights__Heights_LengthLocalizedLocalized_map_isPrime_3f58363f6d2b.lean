-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_map_isPrime_3f58363f6d2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:36.911623+00:00
-- url     : https://prove2.me/submissions/8e095497-d797-415b-9aad-6123fc5573e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized

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
universe u v
namespace GroundTheory.Heights₂.Heights
namespace LengthLocalizedLocalized
theorem _root_.solution (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ P hP
    (Set.disjoint_left.mpr fun _ hx hxP => hx (h hxP))
end LengthLocalizedLocalized
end GroundTheory.Heights₂.Heights
