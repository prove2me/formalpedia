-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.retryTwelveMissProbability_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:24:43.812348+00:00
-- url     : https://prove2.me/submissions/2479208f-0d89-45c8-b950-449dba655b53

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_twelve_exponential_bound


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
namespace QEC.Distillation.PhaseInjection
theorem _root_.solution
    (start target : ZMod 12) (blocks : Nat) :
    retryTwelveMissProbability blocks start target ≤ (4095 / 4096 : Real) ^ blocks :=
  PhaseRetry.targetMissProbability_twelve_exponential_bound start target blocks
end QEC.Distillation.PhaseInjection
