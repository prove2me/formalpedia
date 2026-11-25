-- Prove2me | solution 1 for PIW.AdelClassFin.DictLat.iv_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:35.174012+00:00
-- url     : https://prove2.me/submissions/93493ec6-952f-4f06-9ec7-6b9aff09b15a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
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
namespace PIW.AdelClassFin
namespace DictLat
theorem _root_.solution (I : AutInst) (i : Fin I.n) :
    iv I (Pi.single i (1 : I.E)) = Pi.single i (1 : I.E ⊗[I.F] Af I.F) := by
  funext j
  simp only [iv, Pi.single_apply]
  split_ifs <;> simp
end DictLat
end PIW.AdelClassFin
