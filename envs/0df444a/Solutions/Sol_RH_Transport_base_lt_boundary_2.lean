-- Prove2me | solution 2 for RH.Transport.base_lt_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:42.262206+00:00
-- url     : https://prove2.me/submissions/4dd2eb12-52be-45b8-abbc-5ed603bd3089

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation

set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution {B β ω σ : ℝ} (hω : 0 < ω) :
    B < continuationBoundary B β ω σ := by
  have h := le_max_left (B + ω) (β - σ)
  change B < max (B + ω) (β - σ)
  linarith
end RH.Transport
