-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseCycleAngle_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:11:33.890307+00:00
-- url     : https://prove2.me/submissions/116c605d-e4eb-48bb-a170-c3d2a5ecbfd6

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution : phaseCycleAngle 8 = -Real.pi / 4 := by
  norm_num [phaseCycleAngle]
  ring
end QEC.Distillation.PhaseInjection
