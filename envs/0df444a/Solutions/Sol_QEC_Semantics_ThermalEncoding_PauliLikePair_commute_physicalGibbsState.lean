-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.commute_physicalGibbsState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:11:48.713968+00:00
-- url     : https://prove2.me/submissions/0380b0aa-0479-477f-b794-5ea5115e2ba8

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalGibbsState_toOperator_eq_normalized_exp
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.clbtFiniteQuantumSystemComplete
namespace QEC.Semantics
namespace ThermalEncoding.PauliLikePair
theorem _root_.solution
    {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
    (logical : ThermalEncoding.PauliLikePair K)
    [Nontrivial logical.AuxiliarySpace]
    (hamiltonian A : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (hA : Commute A hamiltonian)
    (beta : ℝ) :
    Commute A
      (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator := by
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  rw [logical.physicalGibbsState_toOperator_eq_normalized_exp
    hamiltonian hX hZ hhamiltonian beta]
  let Ac : ContinuousOperator K := LinearMap.toContinuousLinearMap A
  let Hc : ContinuousOperator K := LinearMap.toContinuousLinearMap hamiltonian
  have hcontinuous : Commute Ac Hc := by
    rw [Commute]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun T : Operator K => T x) hA.eq
  have hexp : Commute Ac (NormedSpace.exp ((-beta : ℂ) • Hc)) :=
    (hcontinuous.smul_right (-beta : ℂ)).exp_right
  rw [Commute]
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun T : ContinuousOperator K => T x) hexp.eq
  have hxscaled := congrArg (fun y : K =>
    ((ThermalEncoding.gibbsPartitionFunction beta
      (logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian) : ℂ)⁻¹) • y) hx
  simpa [Ac, Hc, Module.End.mul_apply, mul_smul] using hxscaled
end ThermalEncoding.PauliLikePair
end QEC.Semantics
