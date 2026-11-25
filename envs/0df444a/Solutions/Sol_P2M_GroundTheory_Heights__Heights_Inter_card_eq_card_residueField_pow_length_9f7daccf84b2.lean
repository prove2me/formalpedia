-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:18:50.287038+00:00
-- url     : https://prove2.me/submissions/af51d604-ca3f-46ec-9b93-975c5212ce10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7

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
open IsLocalRing
universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (Module.length R M).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  rw [← hn, ENat.toNat_natCast]
  exact card_eq_pow_of_length_eq n M hn.symm
end GroundTheory.Heights₂.Heights.Inter
