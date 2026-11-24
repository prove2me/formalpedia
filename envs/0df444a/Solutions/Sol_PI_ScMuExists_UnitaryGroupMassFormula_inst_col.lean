-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:11:01.78329+00:00
-- url     : https://prove2.me/submissions/08966060-0194-4415-b23a-8b88a584a964

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
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
open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (j : Fin r ⊕ Fin r ⊕ Unit) :
    instBmat I v e f z *ᵥ Pi.single j 1 = rv I v (instFvec e f z j) := by
  ext i
  rw [Matrix.mulVec_single_one]
  simp [instBmat]
end PI.ScMuExists.UnitaryGroupMassFormula
