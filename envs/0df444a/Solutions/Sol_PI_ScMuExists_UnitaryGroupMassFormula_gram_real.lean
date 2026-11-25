-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.gram_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:21.947496+00:00
-- url     : https://prove2.me/submissions/704f685e-6c4b-47e1-833d-d3fa601a25bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
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
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (v : NumberField.InfinitePlace I.F) :
    ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ = I.J.map (I.φ v) := by
  have h : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have e : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h, Matrix.conjTranspose_one]
  rw [← I.P_spec v]
  calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹
      = (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by rw [e, h, Matrix.one_mul, Matrix.mul_one]
end PI.ScMuExists.UnitaryGroupMassFormula
