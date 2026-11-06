-- Prove2me | solution 1 for RH.Transport.continuationBoundary_eq_sub_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:06.173212+00:00
-- url     : https://prove2.me/submissions/dcd241a3-1a09-474f-80d6-07a78bf9849e

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation

set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution (B β ω σ : ℝ) :
    continuationBoundary B β ω σ = β - continuationMargin B β ω σ := by
  unfold continuationBoundary continuationMargin
  rcases le_total (β - B - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]
end RH.Transport
