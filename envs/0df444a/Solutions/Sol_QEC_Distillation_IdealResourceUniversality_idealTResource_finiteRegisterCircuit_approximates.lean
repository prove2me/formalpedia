-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.idealTResource_finiteRegisterCircuit_approximates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:44:41.219118+00:00
-- url     : https://prove2.me/submissions/5d5c1482-ef60-47b8-bfc7-0e50deb2cc70

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Theorems.Thm_QEC_Distillation_IdealResourceUniversality_tResource_projectivelyGeneratedDense
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense


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
theorem _root_.solution
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (circuit : FiniteRegisterCircuit Wire)
    (precision : Real) (hprecision : 0 < precision) :
    ApproximatesModuloPhase
      (finiteRegisterGenerators (Wire := Wire) tResourceGenerators)
      circuit.unitary precision :=
  finiteRegisterCircuit_approximates_of_projectivelyGeneratedDense
    tResourceGenerators tResource_projectivelyGeneratedDense
    circuit precision hprecision
end QEC.Distillation.IdealResourceUniversality
