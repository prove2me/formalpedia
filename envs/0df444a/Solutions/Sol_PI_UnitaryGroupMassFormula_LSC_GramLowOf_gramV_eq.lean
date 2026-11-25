-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.GramLowOf.gramV_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:13.684442+00:00
-- url     : https://prove2.me/submissions/b32e02de-c641-42e7-9518-3437544c4a1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
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
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.GramLowOf
namespace PI.UnitaryGroupMassFormula.LSC.GramLowOf
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) :
    Size.gramV I x v b =
      ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i)))ᴴ *
        ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i))) := by
  ext a c
  simp only [Size.gramV, Size.coordV, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
end PI.UnitaryGroupMassFormula.LSC.GramLowOf
