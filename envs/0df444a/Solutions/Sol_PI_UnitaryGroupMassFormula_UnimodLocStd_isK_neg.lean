-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:53.191687+00:00
-- url     : https://prove2.me/submissions/93889c6f-96ff-4a4d-a52a-6371fdd49e0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {t : ℂ} (h : IsK b d t) : IsK b d (-t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨-p, -q, r, hr, ?_⟩
  push_cast
  linear_combination -h
end PI.UnitaryGroupMassFormula.UnimodLocStd
