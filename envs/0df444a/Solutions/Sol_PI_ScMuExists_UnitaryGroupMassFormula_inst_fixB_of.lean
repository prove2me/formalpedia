-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_fixB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:04.37793+00:00
-- url     : https://prove2.me/submissions/dca8dfae-4d05-44da-844b-73c08ed0f97b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstTop
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_mem_frameSet
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_col
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
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ)
    (hm : ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x) : m * instBmat I v e f z = instBmat I v e f z := by
  have hcol : ∀ j, (m * instBmat I v e f z) *ᵥ Pi.single j 1 = instBmat I v e f z *ᵥ Pi.single j 1 := by
    intro j
    rw [← Matrix.mulVec_mulVec, inst_col v e f z j, hm _ (inst_mem_frameSet e f z j)]
  ext i j
  have h := congrFun (hcol j) i
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h
end PI.ScMuExists.UnitaryGroupMassFormula
