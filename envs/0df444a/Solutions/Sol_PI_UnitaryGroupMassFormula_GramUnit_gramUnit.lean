-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramUnit.gramUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:18.801608+00:00
-- url     : https://prove2.me/submissions/3aa03419-507c-4d3f-8175-42c2a0c12edd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramUnitMultiplication_BeMulByZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramUnit_be_mulBy_zero

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
theorem _root_.solution : GramUnit := by
  intro p _ l ex ph hD n de hde
  calc PI.FglGram.GramRhs l ex ph de = (∑ j, PI.FglGram.phAt ph (PI.FglGram.Xv j) : MvPowerSeries (Fin n) ℂ_[p]) + 0 := by
        unfold PI.FglGram.GramRhs
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by
            rw [hde j j, if_pos rfl, Prod.fst_one, map_one, one_mul]
        · exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' hj' => by
            rw [hde j j', if_neg (ne_of_lt (Finset.mem_filter.mp hj').2), Prod.fst_zero]
            exact be_mulBy_zero l ex ph hD _ _ (MvPowerSeries.constantCoeff_X _)
    _ = _ := add_zero _
end PI.UnitaryGroupMassFormula.GramUnit
