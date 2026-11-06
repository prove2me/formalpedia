-- Prove2me | solution 2 for RH.Transport.continuationMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:40.427292+00:00
-- url     : https://prove2.me/submissions/d97ceeaf-5290-43ca-85b6-2750216353e0

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation

set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution {B β ω σ : ℝ}
    (hω : ω < β - B) (hσ : 0 < σ) :
    0 < continuationMargin B β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ
end RH.Transport
