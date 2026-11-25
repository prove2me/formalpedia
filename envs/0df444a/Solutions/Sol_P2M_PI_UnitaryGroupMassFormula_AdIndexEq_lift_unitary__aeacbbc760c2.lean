-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_AdIndexEq_lift_unitary__aeacbbc760c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:10.042795+00:00
-- url     : https://prove2.me/submissions/3219b763-0d3b-4f68-b05c-d2ee0616a2db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_CompactLocalGlobal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_liftMat_unitary
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution : LiftU := by
  intro I v g hg
  refine ⟨⟨liftGL I v g, liftMat_unitary I v g hg⟩, ?_, ?_⟩
  · apply Units.ext
    first
    | exact liftMat_map_same I v g.val
    | simpa [matV, Formalism.UG.bc, liftGL] using liftMat_map_same I v g.val
  · intro w hw
    apply Units.ext
    first
    | exact liftMat_map_ne I hw g.val
    | simpa [matV, Formalism.UG.bc, liftGL] using liftMat_map_ne I hw g.val
end PI.UnitaryGroupMassFormula.AdIndexEq
