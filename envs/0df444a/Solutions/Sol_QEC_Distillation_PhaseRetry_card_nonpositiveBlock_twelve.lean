-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.card_nonpositiveBlock_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:42.231053+00:00
-- url     : https://prove2.me/submissions/0f769e76-c3f2-405c-8d7d-3b8287b54305

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution :
    Fintype.card (NonpositiveBlock 12) = 4095 := by
  decide +kernel
end QEC.Distillation.PhaseRetry
