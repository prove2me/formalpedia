-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:30.488796+00:00
-- url     : https://prove2.me/submissions/a8b42943-654a-43c5-8d2b-95a203e1740f

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
theorem _root_.solution {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) :
    SatMem l Λ ((r : ℂ) • v) := by
  obtain ⟨n, hn, hv⟩ := hv
  refine ⟨n, hn, ?_⟩
  rw [smul_comm, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hv r
end PI.UnitaryGroupMassFormula.UnimodLocStd
