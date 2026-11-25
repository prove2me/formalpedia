-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_Kset_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:11.155093+00:00
-- url     : https://prove2.me/submissions/e92851e4-2373-4162-b6eb-bc92d8232b1b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstPlace
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_Jm_conjTranspose
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
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    star g ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg star hg.2
  simp only [star_mul, Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose] at h
  simpa [Matrix.star_eq_conjTranspose] using h.symm
end PI.ScMuExists.UnitaryGroupMassFormula
