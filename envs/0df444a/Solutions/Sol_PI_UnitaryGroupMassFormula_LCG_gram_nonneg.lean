-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.gram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:54.780799+00:00
-- url     : https://prove2.me/submissions/f00d7fab-71c2-4324-bea2-9a510b66bae5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatticeIsDiscreteGroup
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
theorem _root_.solution (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) : 0 ≤ ((gramV I z v b).det).re := by
  let C : Matrix (Fin I.n) (Fin j) ℂ := Matrix.of fun i a => coordV I z v (b a) i
  have hG : gramV I z v b = Cᴴ * C := by
    ext a c
    simp [gramV, C, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG]
  exact (hDM I.n j C 1 1 zero_le_one (fun w => by simp)).1
end PI.UnitaryGroupMassFormula.LCG
