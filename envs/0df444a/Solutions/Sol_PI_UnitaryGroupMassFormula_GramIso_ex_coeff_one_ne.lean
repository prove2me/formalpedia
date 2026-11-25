-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramIso.ex_coeff_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:46.195483+00:00
-- url     : https://prove2.me/submissions/401b0069-578d-4d55-acb7-22e4b7730162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_l_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramIso
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.GramIso
theorem _root_.solution (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 ex ≠ 0 := by
  intro h1
  have hlc := l_const l ex he hl
  have h2 : ((2 : ℕ) : ℕ∞) ≤ ex.order := by
    apply PowerSeries.nat_le_order
    intro i hi
    interval_cases i
    · simpa using he
    · exact h1
  have h3 := PowerSeries.le_order_subst_right' (φ := l) he hlc
  rw [hl, PowerSeries.order_X] at h3
  have h4 := h2.trans h3
  norm_num at h4
end PI.UnitaryGroupMassFormula.GramIso
