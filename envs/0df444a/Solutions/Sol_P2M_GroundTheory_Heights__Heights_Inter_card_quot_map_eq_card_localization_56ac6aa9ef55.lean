-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:28.695192+00:00
-- url     : https://prove2.me/submissions/91f4bed8-f0fb-4fe0-b55b-eb162014e041

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] [IsLocalization.AtPrime S (p.comap (Ideal.Quotient.mk I))] :
    Nat.card (S ⧸ I.map (algebraMap R S)) = Nat.card (Localization.AtPrime p) := by
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) (p.comap (Ideal.Quotient.mk I)).primeCompl = p.primeCompl := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨r', hr', he⟩
      rw [← he]
      exact hr'
    · intro hx
      exact ⟨r, hx, rfl⟩
  have : IsLocalization p.primeCompl (S ⧸ I.map (algebraMap R S)) := hM ▸ inferInstance
  exact Nat.card_congr (IsLocalization.algEquiv p.primeCompl _ (Localization.AtPrime p)).toEquiv
end GroundTheory.Heights₂.Heights.Inter
