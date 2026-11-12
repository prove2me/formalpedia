-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseInjectionStoppingHitMass_eight_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:31.481941+00:00
-- url     : https://prove2.me/submissions/0feca919-d0f2-479f-8349-9ae758a4d144

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingMissMass_eq_targetMissProbability
import Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_eight_target_hit_probability_one


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
    (start target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks) start target psi hpsi)
      Filter.atTop (nhds 1) := by
  convert PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one start target using 1
  funext blocks
  unfold phaseInjectionStoppingHitMass
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  rfl
end QEC.Distillation.PhaseInjection
