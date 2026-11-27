-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.sv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:18.046402+00:00
-- url     : https://prove2.me/submissions/b679414e-14d2-43c3-96e8-cb936ae0b344

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
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
variable {E : Type} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {k : ℕ} (s : Fin k → E) (b : Fin k → Fin n → E) :
    sv (∑ a, starRingEnd E (s a) • b a) = ∑ a, s a • sv (b a) := by
  funext i
  simp [sv, Finset.sum_apply, map_sum, map_mul]
end PI.UnitaryGroupMassFormula.LCG
