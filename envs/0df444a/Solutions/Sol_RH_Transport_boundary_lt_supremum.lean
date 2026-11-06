-- Prove2me | solution 1 for RH.Transport.boundary_lt_supremum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:06.94254+00:00
-- url     : https://prove2.me/submissions/6180af6a-5481-426e-b690-69d29692f05e

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
    continuationBoundary B β ω σ < β := by
  exact max_lt (by linarith) (by linarith)
end RH.Transport
