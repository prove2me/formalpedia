-- Prove2me | solution 1 for P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:41.006412+00:00
-- url     : https://prove2.me/submissions/95b4fb0e-b945-4166-952f-c1aad70868bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwining
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Theorems.Thm_GlobalTheory_re_inner_le_on_image_of_intertwining


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T] [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T) (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) → (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) → ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  first | exact @GlobalTheory.re_inner_le_on_image_of_intertwining | exact GlobalTheory.re_inner_le_on_image_of_intertwining | (intros; apply GlobalTheory.re_inner_le_on_image_of_intertwining <;> assumption)
end _root_.GlobalTheory.T
