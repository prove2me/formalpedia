-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_QJQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:25.883028+00:00
-- url     : https://prove2.me/submissions/3f7fe4ce-b93a-4fe2-8839-4fdccaebc189

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_inUJ
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_hP
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
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (y : I.GA) (v : InfinitePlace I.F) :
    (qM I y v)ᴴ * Formalism.REAL.Jm (I.ε v) * qM I y v = I.J.map (I.φ v) := by
  unfold qM
  rw [Matrix.conjTranspose_mul]
  have hU := ap_inUJ (y.1 v)⁻¹
  have hS := I.P_spec v
  calc ((I.P v)⁻¹)ᴴ * (Formalism.MainNotions.S.uMat (y.1 v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (Formalism.MainNotions.S.uMat (y.1 v)⁻¹ * (I.P v)⁻¹)
      = ((I.P v)⁻¹)ᴴ * ((Formalism.MainNotions.S.uMat (y.1 v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * Formalism.MainNotions.S.uMat (y.1 v)⁻¹) * (I.P v)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹ := by rw [hU]
    _ = ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ := by rw [hS]
    _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = I.J.map (I.φ v) := by
        rw [ap_hP]
        simp
end PI.UnitaryGroupMassFormula.LCG
