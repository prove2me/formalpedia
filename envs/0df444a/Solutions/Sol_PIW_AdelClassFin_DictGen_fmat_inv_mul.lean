-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.fmat_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:14.832224+00:00
-- url     : https://prove2.me/submissions/db578275-82a2-41ea-82ec-1b9cf19328fc

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
theorem _root_.solution (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  first
    | exact Units.inv_mul (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp
end PIW.AdelClassFin.DictGen
