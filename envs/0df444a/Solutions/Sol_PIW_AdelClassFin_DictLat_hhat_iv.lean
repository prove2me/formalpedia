-- Prove2me | solution 1 for PIW.AdelClassFin.DictLat.hhat_iv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:12.179489+00:00
-- url     : https://prove2.me/submissions/b28ecda1-6fa7-4b5f-9b2d-36ff2bc1e937

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
theorem _root_.solution (I : AutInst) (v w : Fin I.n → I.E) :
    hhat I (iv I v) (iv I w) = Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J v w) := by
  simp [hhat, iv, Formalism.UG.hform, DictLat.sigR_inclE, map_sum, map_mul, starRingEnd_apply]
end DictLat
end PIW.AdelClassFin
