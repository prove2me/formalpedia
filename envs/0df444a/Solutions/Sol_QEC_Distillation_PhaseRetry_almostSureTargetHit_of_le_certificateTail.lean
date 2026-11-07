-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.almostSureTargetHit_of_le_certificateTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:39:44.058195+00:00
-- url     : https://prove2.me/submissions/0255f975-9d57-49d5-a127-9a7542a4c993

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution
    {q : Nat} {failure : Nat → Real}
    (hNonnegative : ∀ blocks, 0 ≤ failure blocks)
    (hBound : ∀ blocks, failure blocks ≤ certificateFailureTail q blocks)
    (hTail : AlmostSureTargetHit (certificateFailureTail q)) :
    AlmostSureTargetHit failure := by
  unfold AlmostSureTargetHit at hTail ⊢
  exact squeeze_zero hNonnegative hBound hTail
end QEC.Distillation.PhaseRetry
