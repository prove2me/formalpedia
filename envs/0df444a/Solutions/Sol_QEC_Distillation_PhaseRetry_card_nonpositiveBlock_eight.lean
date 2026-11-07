-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.card_nonpositiveBlock_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:40.419171+00:00
-- url     : https://prove2.me/submissions/b713c31c-12d4-4026-bc78-bc53f311b647

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution :
    Fintype.card (NonpositiveBlock 8) = 255 := by
  decide +kernel
end QEC.Distillation.PhaseRetry
