-- Prove2me | solution 1 for RH.Transport.strip_boundary_margins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:51.435201+00:00
-- url     : https://prove2.me/submissions/77d180ef-0f32-493c-9ecd-9f3862172e4a

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
import Theorems.Thm_RH_Transport_continuationMargin_pos
import Theorems.Thm_RH_Transport_boundary_lt_supremum
import Theorems.Thm_RH_Transport_base_lt_boundary
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_pos


set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution {B β ω σ : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hβ : β ≤ 1)
    (hω0 : 0 < ω) (hω : ω < β - B) (hσ : 0 < σ) :
    (1 / 2 : ℝ) < continuationBoundary B β ω σ ∧
      B < continuationBoundary B β ω σ ∧
      continuationBoundary B β ω σ < β ∧
      continuationBoundary B β ω σ < 1 ∧
      0 < continuationMargin B β ω σ := by
  have hleft := base_lt_boundary (B := B) (β := β) (σ := σ) hω0
  have hright := boundary_lt_supremum hω hσ
  exact ⟨hB.trans hleft, hleft, hright, hright.trans_le hβ,
    continuationMargin_pos hω hσ⟩
end RH.Transport
