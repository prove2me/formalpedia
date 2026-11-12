-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.retryEightMissProbability_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:24:39.890367+00:00
-- url     : https://prove2.me/submissions/116030f3-86c9-4c86-80d9-09d9572e4845

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseRetry_targetMissProbability_eight_exponential_bound


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
    (start target : ZMod 8) (blocks : Nat) :
    retryEightMissProbability blocks start target ≤ (255 / 256 : Real) ^ blocks :=
  PhaseRetry.targetMissProbability_eight_exponential_bound start target blocks
end QEC.Distillation.PhaseInjection
