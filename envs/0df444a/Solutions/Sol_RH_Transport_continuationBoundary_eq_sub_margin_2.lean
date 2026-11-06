-- Prove2me | solution 2 for RH.Transport.continuationBoundary_eq_sub_margin
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:11:46.672598+00:00
-- url     : https://prove2.me/submissions/2c665266-ab3b-4a86-bd7d-34d634c207a2

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation

theorem solution (B β ω σ : ℝ) :
    continuationBoundary B β ω σ = β - continuationMargin B β ω σ := by
  rw [continuationBoundary, continuationMargin, ← max_sub_sub_left]
  congr 1 <;> ring
