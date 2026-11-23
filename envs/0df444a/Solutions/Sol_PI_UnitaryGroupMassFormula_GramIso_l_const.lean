-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramIso.l_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:37.020419+00:00
-- url     : https://prove2.me/submissions/c74d9b0b-2ac5-4e37-805a-5db78209e53b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe

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
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h0 : PowerSeries.HasSubst (0 : PowerSeries ℂ_[p]) := PowerSeries.HasSubst.zero'
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' he
  have key := congrArg (PowerSeries.subst (0 : PowerSeries ℂ_[p])) hl
  rw [PowerSeries.subst_comp_subst_apply hex h0, PowerSeries.subst_zero_of_constantCoeff_zero he,
    PowerSeries.subst_X h0, PowerSeries.subst_zero_eq_C_constantCoeff] at key
  have := congrArg MvPowerSeries.constantCoeff key
  simpa using this
end PI.UnitaryGroupMassFormula.GramIso
