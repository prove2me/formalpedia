-- Prove2me | solution 1 for RH.Transport.base_lt_boundary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:58:28.500279+00:00
-- url     : https://prove2.me/submissions/d6001063-e8f3-4585-b855-6f01bbfc9e1a

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation

theorem solution {B β ω σ : ℝ} (hω : 0 < ω) :
    B < continuationBoundary B β ω σ := by
  rw [continuationBoundary]
  exact (lt_add_of_pos_right B hω).trans_le (le_max_left (B + ω) (β - σ))
