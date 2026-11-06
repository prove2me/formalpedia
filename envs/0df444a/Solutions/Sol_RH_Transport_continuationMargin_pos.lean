-- Prove2me | solution 1 for RH.Transport.continuationMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:59:27.054095+00:00
-- url     : https://prove2.me/submissions/85a0698c-0acf-4961-8164-f1f28c7c01f2

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
  unfold RH.Transport.continuationMargin
  exact lt_min (by linarith) hσ
