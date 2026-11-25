-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:51:08.533128+00:00
-- url     : https://prove2.me/submissions/f223caa9-cdab-4fc3-888d-64caaf0804cc

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
theorem _root_.solution {v : m → ℂ} (hv : SatMem l Λ v) : SatMem l Λ (-v) := by
  obtain ⟨n, hn, hnv⟩ := hv
  exact ⟨n, hn, by rw [smul_neg]; exact Λ.neg_mem hnv⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
