-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.hsN_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:50.838982+00:00
-- url     : https://prove2.me/submissions/0134cac8-4c11-4c75-ab0f-a64e7af7f0fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
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
open PI.LatCountG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsN, Formalism.REAL.hs]
end PI.UnitaryGroupMassFormula.LCG
