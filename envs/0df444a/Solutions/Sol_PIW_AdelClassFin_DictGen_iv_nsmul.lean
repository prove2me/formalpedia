-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.iv_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:39.012734+00:00
-- url     : https://prove2.me/submissions/84c492e0-3226-4015-99cb-517ef2d54427

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
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
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution (N : ℕ) (v : Fin I.n → I.E) :
    iv I (N • v) = (N : I.E ⊗[I.F] Af I.F) • iv I v := by
  funext i
  first
    | simp [iv, nsmul_eq_mul]
    | simp only [iv, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul]
end PIW.AdelClassFin.DictGen
