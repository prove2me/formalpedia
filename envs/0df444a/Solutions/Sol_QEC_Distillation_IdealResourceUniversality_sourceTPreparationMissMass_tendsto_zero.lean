-- Prove2me | solution 1 for QEC.Distillation.IdealResourceUniversality.sourceTPreparationMissMass_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:24:19.756164+00:00
-- url     : https://prove2.me/submissions/157a6584-148c-460f-94ac-5fd032236a1d

import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
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
theorem _root_.solution :
    Filter.Tendsto sourceTPreparationMissMass Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun attempts : Nat =>
      (1 / 3 : Real) ^ attempts) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hpow.congr' (Filter.Eventually.of_forall fun attempts =>
    (sourceTPreparationMissMass_eq_pow attempts).symm)
end QEC.Distillation.IdealResourceUniversality
