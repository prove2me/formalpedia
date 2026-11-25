-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramUnit.be_mulBy_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:16.782534+00:00
-- url     : https://prove2.me/submissions/1c7bc84f-a8a8-4fa8-a171-40b5f7e14924

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramUnit_inv_of_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramUnit
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.GramUnit
theorem _root_.solution (l ex ph : PowerSeries ℂ_[p]) (hD : Data l ex ph) {σ : Type*}
    (a b : MvPowerSeries σ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph (mulBy l ex 0 a) b = 0 := by
  obtain ⟨h0, hle, hph⟩ := hD
  have hl := inv_of_left l ex h0 hle
  have hHl : HasSubst l := HasSubst.of_constantCoeff_zero' hl.2
  have hHb : HasSubst b := HasSubst.of_constantCoeff_zero hb
  have hs0 : PI.FglGram.mulBy l ex 0 a = 0 := by
    simp only [PI.FglGram.mulBy, PI.FglGram.pt, map_zero, zero_mul]
    exact subst_zero_of_constantCoeff_zero h0
  have hadd : PI.FglGram.add l ex 0 b = b := by
    simp only [PI.FglGram.add, PI.FglGram.pt, PI.FglGram.lg]
    rw [subst_zero_of_constantCoeff_zero hl.2, zero_add, ← subst_comp_subst_apply hHl hHb, hl.1,
      subst_X hHb]
  simp only [PI.FglGram.be, hs0, hadd, PI.FglGram.phAt, subst_zero_of_constantCoeff_zero hph, sub_zero,
    sub_self]
end PI.UnitaryGroupMassFormula.GramUnit
