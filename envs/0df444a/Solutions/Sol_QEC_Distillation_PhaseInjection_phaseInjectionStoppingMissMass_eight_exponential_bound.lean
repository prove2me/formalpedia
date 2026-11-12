-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseInjectionStoppingMissMass_eight_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:25:31.401191+00:00
-- url     : https://prove2.me/submissions/1a467659-6c27-48e3-840f-d13115d3a86c

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingMissMass_eq_targetMissProbability
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
    (blocks : Nat) (start target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi ≤
      (255 / 256 : Real) ^ blocks := by
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  exact PhaseRetry.targetMissProbability_eight_exponential_bound start target blocks
end QEC.Distillation.PhaseInjection
