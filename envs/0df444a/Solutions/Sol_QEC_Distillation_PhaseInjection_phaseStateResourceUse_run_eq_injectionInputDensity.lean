-- Prove2me | solution 1 for QEC.Distillation.PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:35:30.831073+00:00
-- url     : https://prove2.me/submissions/7d775661-ad9f-458e-8ff3-a7b89ccf091f

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Definitions.Def_QEC_Distillation_Injection_PhaseInjection
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_ZeroPreparationAdapter_run_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
private theorem densityOperator_ext_toOperator {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H} (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem sourceInputDensity_toOperator (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (sourceInputDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [sourceInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, hpsi]
  norm_num
private theorem injectionInputDensity_toOperator (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) :
    (injectionInputDensity psi theta hpsi).toOperator =
      (InnerProductSpace.rankOne Complex (injectionInput psi theta)
        (injectionInput psi theta)).toLinearMap := by
  rw [injectionInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, injectionInput_norm psi theta hpsi]
  norm_num
end PhaseInjection
end Distillation
end QEC
end
end

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
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    (phaseStateResourceUse theta).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi theta hpsi := by
  apply densityOperator_ext_toOperator
  rw [AdaptiveIdealClifford.ResourceUse.run_toOperator]
  change (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport)
    (DensityOperator.tensorDensity (sourceInputDensity psi hpsi)
      (OneQubitMagic.phaseStateDensity theta)).toOperator = _
  rw [QuantumChannel.unitaryConj_apply,
    DensityOperator.tensorDensity_toOperator,
    sourceInputDensity_toOperator,
    OneQubitMagic.phaseStateDensity_toOperator,
    DensityOperator.tensorMap_rankOne,
    QuditSubsystem.conjOperator_rankOne,
    injectionInputDensity_toOperator]
  rfl
end QEC.Distillation.PhaseInjection
