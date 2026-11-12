-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.hResource_targetAction_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:20:06.807506+00:00
-- url     : https://prove2.me/submissions/804f5b73-55eb-4005-94ad-0cfeee410bb0

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseEightTargetAction_eq


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
    phaseCycleTargetAction 8 (1 : ZMod 8) =
      phaseShiftOperator (-Real.pi / 4) := by
  change phaseEightTargetAction (1 : ZMod 8) =
    phaseShiftOperator (-Real.pi / 4)
  rw [phaseEightTargetAction_eq]
  have hval : (1 : ZMod 8).val = 1 := ZMod.val_one'' (by norm_num)
  rw [hval, Nat.cast_one, mul_one]
end QEC.Distillation.IdealResourceUniversality
