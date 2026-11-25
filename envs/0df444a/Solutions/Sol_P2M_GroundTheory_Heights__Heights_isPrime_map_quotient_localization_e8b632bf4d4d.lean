-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isPrime_map_quotient_localization_e8b632bf4d4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:15.320469+00:00
-- url     : https://prove2.me/submissions/f52cbdd7-dd65-459f-bc33-f2a1f2b4abf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    (hWm : W ≤ m) (hIW : I ≤ W) :
    (W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m)))).IsPrime := by
  rw [← Ideal.map_map]
  have hd : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m) W ‹_› hd
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.map_mono hIW)
end GroundTheory.Heights₂.Heights
