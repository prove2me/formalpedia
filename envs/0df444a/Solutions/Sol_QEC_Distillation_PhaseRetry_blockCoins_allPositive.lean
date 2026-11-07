-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.blockCoins_allPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:39:07.281692+00:00
-- url     : https://prove2.me/submissions/95c3edac-416b-47d2-960b-49483951db44

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (q : Nat) :
    blockCoins (allPositiveBlock q) = positiveBlock q := by
  exact List.ofFn_const q true
end QEC.Distillation.PhaseRetry
