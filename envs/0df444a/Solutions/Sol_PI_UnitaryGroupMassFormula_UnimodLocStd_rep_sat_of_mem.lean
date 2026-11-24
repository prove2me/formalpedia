-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:58:06.381911+00:00
-- url     : https://prove2.me/submissions/a3b7c19d-5496-43d7-9ee0-d5500711a61b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic

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
theorem _root_.solution {v : m → ℂ} (hv : v ∈ Λ) (hl : l.Prime) : SatMem l Λ v :=
  ⟨1, by simpa using hl.one_lt.ne' ∘ Nat.dvd_one.mp, by simpa using hv⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
