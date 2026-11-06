-- Prove2me | solution 3 for RH.Transport.continuationMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:28.022206+00:00
-- url     : https://prove2.me/submissions/41f53ce0-cdb5-47ee-9e9d-b803e9ab319f

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_pos

set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
theorem solution {B β ω σ : ℝ}
    (hω : ω < β - B) (hσ : 0 < σ) :
    0 < continuationMargin B β ω σ := by
  unfold continuationMargin
  exact lt_min (by linarith) hσ
