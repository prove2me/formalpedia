-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:34.447269+00:00
-- url     : https://prove2.me/submissions/3f4bc5af-633f-4b85-8b9d-266b1f8f7052

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
theorem _root_.solution (A : Type*) [CommRing A] [Finite A] [Fintype (PrimeSpectrum A)] :
    Real.log (Nat.card A) = ∑ p : PrimeSpectrum A, Real.log (Nat.card (Localization.AtPrime p.asIdeal)) := by
  have hA : Nat.card A = ∏ p : PrimeSpectrum A, Nat.card (Localization.AtPrime p.asIdeal) := by
    rw [Nat.card_congr (PrimeSpectrum.toPiLocalizationEquiv A).toEquiv, Nat.card_pi]
  have h0 : Nat.card A ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hA, Finset.prod_ne_zero_iff] at h0
  rw [hA, Nat.cast_prod, Real.log_prod fun p _ => by exact_mod_cast h0 p (Finset.mem_univ _)]
end GroundTheory.Heights₂.Heights.Inter
