-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:45.0969+00:00
-- url     : https://prove2.me/submissions/88af2bdf-699a-4554-8e4d-e4c7486dff0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength

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
theorem _root_.solution (N : Type v) [AddCommGroup N] [Module R N]
    [IsSimpleModule R N] : Nat.card N = Nat.card (ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R N›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact Nat.card_congr e.toEquiv
end GroundTheory.Heights₂.Heights.Inter
