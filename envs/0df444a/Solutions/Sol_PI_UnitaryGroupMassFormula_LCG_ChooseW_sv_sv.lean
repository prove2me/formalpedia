-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.sv_sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:27.789688+00:00
-- url     : https://prove2.me/submissions/2c4fd1d2-7798-4207-9b96-922da47b732e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {E : Type*} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution (w : Fin n → E) : sv (sv w) = w := by
  funext i; simp [sv]
end PI.UnitaryGroupMassFormula.LCG.ChooseW
