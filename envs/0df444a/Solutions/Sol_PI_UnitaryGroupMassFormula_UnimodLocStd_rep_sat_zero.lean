-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:43.738749+00:00
-- url     : https://prove2.me/submissions/62c5bb57-ef6e-4468-9521-9ef65f33d509

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat

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
theorem _root_.solution {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (hl : l.Prime) : SatMem l Λ 0 :=
  ⟨1, hl.not_dvd_one, by rw [smul_zero]; exact zero_mem Λ⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
