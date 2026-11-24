-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:09.106919+00:00
-- url     : https://prove2.me/submissions/f857523a-6459-4e32-8545-4b019fd82232

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
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {t t' : ℂ} (h : IsK b d t) (h' : IsK b d t') : IsK b d (t * t') := by
  obtain ⟨p, q, r, hr, h⟩ := h
  obtain ⟨p', q', r', hr', h'⟩ := h'
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p * p' - q * q' * e, p * q' + q * p' + q * q' * b, r * r', mul_ne_zero hr hr', ?_⟩
  push_cast
  linear_combination ((r' : ℂ) * t') * h + ((p : ℂ) + q * cmTheta b d) * h' - ((q : ℂ) * q') * hn
end PI.UnitaryGroupMassFormula.UnimodLocStd
