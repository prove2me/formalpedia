-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.sourceTPreparationResource_eq_tMagicState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:19:54.843078+00:00
-- url     : https://prove2.me/submissions/46c15379-6f42-4f47-a597-010299b266b9

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTDensity_eq_tMagicState


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
    sourceTDensity = tMagicState :=
  sourceTDensity_eq_tMagicState
end QEC.Distillation.IdealResourceUniversality
