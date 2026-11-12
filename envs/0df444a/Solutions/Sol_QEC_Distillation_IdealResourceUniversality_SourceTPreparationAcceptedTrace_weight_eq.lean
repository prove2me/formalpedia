-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace.weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:11:15.324173+00:00
-- url     : https://prove2.me/submissions/e29873b1-9665-4676-9467-3d668fd42781

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTAttempt_accepted_weight
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTAttempt_rejected_weight


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
open QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace
namespace QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace
theorem _root_.solution (trace : SourceTPreparationAcceptedTrace) :
    trace.weight = (1 / 3 : Real) ^ trace.rejectedAttempts * (2 / 3) := by
  rw [weight, sourceTAttempt_rejected_weight, sourceTAttempt_accepted_weight]
end QEC.Distillation.IdealResourceUniversality.SourceTPreparationAcceptedTrace
