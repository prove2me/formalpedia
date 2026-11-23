-- Prove2me | solution 1 for PI.EF.PK.three_sides
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:13.545593+00:00
-- url     : https://prove2.me/submissions/22477442-e98d-4db0-b6df-4b5a305fd1ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

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
theorem _root_.solution {L B Tp R : ℂ} (h : I * L = B - Tp + I * R) : ‖L‖ ≤ ‖B‖ + ‖Tp‖ + ‖R‖ := by
  have h1 : ‖L‖ = ‖I * L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [h1, h]
  calc ‖B - Tp + I * R‖ ≤ ‖B - Tp‖ + ‖I * R‖ := norm_add_le _ _
    _ ≤ ‖B‖ + ‖Tp‖ + ‖R‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      linarith [norm_sub_le B Tp]
end PI.EF.PK
