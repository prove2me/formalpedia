-- Prove2me | solution 2 for RH.Transport.boundary_lt_supremum
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:58.842953+00:00
-- url     : https://prove2.me/submissions/53c61daa-d6fa-4143-b800-854cd98d9718

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation

theorem solution {B β ω σ : ℝ}
    (hω : ω < β - B) (hσ : 0 < σ) :
    continuationBoundary B β ω σ < β := by
  exact max_lt (by linarith) (by linarith)
