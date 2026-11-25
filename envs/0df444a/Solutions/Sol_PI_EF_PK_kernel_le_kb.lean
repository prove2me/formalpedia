-- Prove2me | solution 1 for PI.EF.PK.kernel_le_kb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:27.169047+00:00
-- url     : https://prove2.me/submissions/83a26682-00f9-4152-9090-2e2648b1cc0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries
namespace PI.EF.PK
theorem _root_.solution (hK : PerronKernel) (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  obtain ⟨h1, h2⟩ := hK y c T hy hc hT
  by_cases h : T * |Real.log y| ≤ 1
  · rw [kb, if_pos h]
    linarith
  · rw [kb, if_neg h]
    push_neg at h
    rw [mul_one_div, le_div_iff₀ (by linarith)]
    linarith
end PI.EF.PK
