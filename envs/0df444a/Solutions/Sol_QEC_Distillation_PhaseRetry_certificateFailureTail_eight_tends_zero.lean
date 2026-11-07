-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.certificateFailureTail_eight_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:56.901226+00:00
-- url     : https://prove2.me/submissions/df1aa113-5064-49a6-9303-b29a184aa240

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution :
    AlmostSureTargetHit (certificateFailureTail 8) := by
  change Filter.Tendsto
    (fun blocks : Nat => (1 - ((2 : Real)⁻¹) ^ 8) ^ blocks)
    Filter.atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
end QEC.Distillation.PhaseRetry
