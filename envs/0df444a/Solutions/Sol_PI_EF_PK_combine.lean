-- Prove2me | solution 1 for PI.EF.PK.combine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:00.809408+00:00
-- url     : https://prove2.me/submissions/36cc1e9a-f938-4e78-8bd2-6e435811d05b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution {B Tp R Lf : ℂ} {b1 b2 b3 : ℝ} (h1 : ‖B‖ ≤ b1) (h2 : ‖Tp‖ ≤ b2) (h3 : ‖Lf‖ ≤ b3) :
    ‖B - Tp + I * R - I * Lf + -(I * R)‖ ≤ b1 + b2 + b3 := by
  have e : B - Tp + I * R - I * Lf + -(I * R) = B - Tp - I * Lf := by ring
  rw [e]
  have hI : ‖I * Lf‖ = ‖Lf‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hs := norm_sub_le (B - Tp) (I * Lf)
  have hs2 := norm_sub_le B Tp
  linarith
end PI.EF.PK
