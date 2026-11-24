-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:18.990017+00:00
-- url     : https://prove2.me/submissions/920d5858-cf2e-4c1a-b6ae-213e3905f730

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
theorem _root_.solution {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t + t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨r' * p + r * p', r' * q + r * q', r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination (r' : ℂ) * h + (r : ℂ) * h'
end PI.UnitaryGroupMassFormula.UnimodLocStd
