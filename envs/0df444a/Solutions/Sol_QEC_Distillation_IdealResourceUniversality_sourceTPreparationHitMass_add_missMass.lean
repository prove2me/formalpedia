-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.sourceTPreparationHitMass_add_missMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:23:45.114721+00:00
-- url     : https://prove2.me/submissions/8a9c4289-46f4-4e22-a911-bbba1167a6b6

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTPreparationHitMass_eq_one_sub_pow
import Theorems.Thm_QEC_Distillation_IdealResourceUniversality_sourceTPreparationMissMass_eq_pow

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
    sourceTPreparationHitMass attemptBudget +
      sourceTPreparationMissMass attemptBudget = 1 := by
  rw [sourceTPreparationHitMass_eq_one_sub_pow,
    sourceTPreparationMissMass_eq_pow]
  ring
end QEC.Distillation.IdealResourceUniversality
