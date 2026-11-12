-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseInjectionStoppingHitMass_twelve_probability_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:54:34.840276+00:00
-- url     : https://prove2.me/submissions/5994c5ea-334a-4548-b6e5-1260959c3f71

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_PhaseInjection_phaseInjectionStoppingMissMass_eq_targetMissProbability
import Theorems.Thm_QEC_Distillation_PhaseRetry_finiteCyclicRetry_twelve_target_hit_probability_one


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
    (start target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks) start target psi hpsi)
      Filter.atTop (nhds 1) := by
  convert PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one start target using 1
  funext blocks
  unfold phaseInjectionStoppingHitMass
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  rfl
end QEC.Distillation.PhaseInjection
