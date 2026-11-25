-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramIso.be_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:15.097193+00:00
-- url     : https://prove2.me/submissions/d5fba42d-930b-4cbc-a946-bd585c020a5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_l_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_ex_comp_l

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
theorem _root_.solution (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {r : ℕ} (j j' : Fin r) :
    be l ex ph (mulBy l ex 0 (Xv j)) (Xv j' : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
  obtain ⟨he, hl, hph⟩ := hD
  have hlc := l_const l ex he hl
  have hinv := ex_comp_l l ex he hl
  simp only [be, mulBy, add, pt, lg, phAt, map_zero, zero_mul]
  rw [PowerSeries.subst_zero_of_constantCoeff_zero he, PowerSeries.subst_zero_of_constantCoeff_zero hlc,
    zero_add, PowerSeries.subst_zero_of_constantCoeff_zero hph, sub_zero,
    ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlc)
      (PowerSeries.HasSubst.X j'), hinv, PowerSeries.subst_X (PowerSeries.HasSubst.X j')]
  exact sub_self _
end PI.UnitaryGroupMassFormula.GramIso
