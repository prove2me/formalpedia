-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_continuous_circle_char_extension__2f18a84957f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:17.652725+00:00
-- url     : https://prove2.me/submissions/5ddc173a-1b39-4a94-80df-f03fc08e7a41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtensionStatement
import Theorems.Thm_GlobalTheory_exists_continuous_circle_char_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  first | exact @GlobalTheory.exists_continuous_circle_char_extension | exact GlobalTheory.exists_continuous_circle_char_extension | (intros; apply GlobalTheory.exists_continuous_circle_char_extension <;> assumption)
end _root_.GlobalTheory.T
