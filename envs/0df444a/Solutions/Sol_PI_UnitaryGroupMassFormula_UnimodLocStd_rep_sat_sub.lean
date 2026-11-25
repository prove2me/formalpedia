-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:56.491561+00:00
-- url     : https://prove2.me/submissions/41422847-9290-426a-a1ce-9c9f7d8c3692

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_neg

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
variable {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ))
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) : SatMem l Λ (v - w) := by
  rw [sub_eq_add_neg]; exact rep_sat_add l Λ hl hv (rep_sat_neg l Λ hw)
end PI.UnitaryGroupMassFormula.UnimodLocStd
