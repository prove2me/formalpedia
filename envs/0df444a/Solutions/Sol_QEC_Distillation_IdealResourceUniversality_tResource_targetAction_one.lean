-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.tResource_targetAction_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:20:47.089798+00:00
-- url     : https://prove2.me/submissions/7e5a89cb-78d4-434d-96af-4d36f7f9aed3

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseTwelveTargetAction_eq


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.IdealResourceUniversality
open QEC.Semantics
open QEC.Semantics.Qubit
open GeneratedUniversality
open OneQubitMagic
open PhaseInjection
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators
namespace QEC.Distillation.IdealResourceUniversality
theorem _root_.solution :
    phaseCycleTargetAction 12 (1 : ZMod 12) =
      phaseShiftOperator (-Real.pi / 6) := by
  change phaseTwelveTargetAction (1 : ZMod 12) =
    phaseShiftOperator (-Real.pi / 6)
  rw [phaseTwelveTargetAction_eq]
  have hval : (1 : ZMod 12).val = 1 := ZMod.val_one'' (by norm_num)
  rw [hval, Nat.cast_one, mul_one]
end QEC.Distillation.IdealResourceUniversality
