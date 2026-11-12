-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.sourceTPreparationMissMass_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:09:38.869276+00:00
-- url     : https://prove2.me/submissions/79f84a51-daf8-4764-99ef-11b912191b33

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
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
namespace QEC.Distillation.IdealResourceUniversality
theorem _root_.solution (attemptBudget : Nat) :
    sourceTPreparationMissMass attemptBudget = (1 / 3 : Real) ^ attemptBudget := by
  rw [sourceTPreparationMissMass, sourceTAttempt_rejected_weight]
end QEC.Distillation.IdealResourceUniversality
