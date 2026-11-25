-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.int_of_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:38.120513+00:00
-- url     : https://prove2.me/submissions/ea7a2bec-d3fe-4328-b60c-78ff1998f391

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_detD_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_area_eq

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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) {t : ℝ} {k : ℤ} (h : t * detD L / area L = k) : ∃ j : ℤ, t = j := by
  have hD := detD_ne L
  rw [area_eq] at h
  rcases abs_choice (detD L) with hA | hA
  · rw [hA, mul_div_assoc, div_self hD, mul_one] at h
    exact ⟨k, h⟩
  · rw [hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one] at h
    exact ⟨-k, by push_cast; linarith⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
