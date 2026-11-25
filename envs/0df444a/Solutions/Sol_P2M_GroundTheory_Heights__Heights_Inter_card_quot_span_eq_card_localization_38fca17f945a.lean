-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:48.314963+00:00
-- url     : https://prove2.me/submissions/708b5b90-c5ec-4c49-9bdb-e62c98dd426f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55

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
theorem _root_.solution {O L : Type*} [CommRing O] [CommRing L] (ψ : O →+* L) (b : O)
    (m : Ideal O) [m.IsPrime] (p : Ideal (O ⧸ Ideal.span {b})) [p.IsPrime]
    (hm : m = p.comap (Ideal.Quotient.mk _)) (h : @IsLocalization O _ m.primeCompl L _ ψ.toAlgebra) :
    Nat.card (L ⧸ Ideal.span {ψ b}) = Nat.card (Localization.AtPrime p) := by
  subst hm
  let _ := ψ.toAlgebra
  rw [← card_quot_map_eq_card_localization (S := L) (Ideal.span {b}) p, Ideal.map_span, Set.image_singleton,
    RingHom.algebraMap_toAlgebra]
end GroundTheory.Heights₂.Heights.Inter
