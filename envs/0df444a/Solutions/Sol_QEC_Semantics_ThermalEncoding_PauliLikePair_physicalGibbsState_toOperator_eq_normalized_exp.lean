-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.physicalGibbsState_toOperator_eq_normalized_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:03.322061+00:00
-- url     : https://prove2.me/submissions/f4d67b10-d1e5-4185-973c-6ac115eb099e

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_physicalHamiltonianEigenbasis_apply
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


section
universe u v
namespace QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
private theorem continuousOperator_exp_smul_apply_eigenvector
    (A : ContinuousOperator H) (v : H) (lambda z : ℂ)
    (hv : A v = lambda • v) :
    NormedSpace.exp (z • A) v = Complex.exp (z * lambda) • v := by
  have hpow : ∀ n : ℕ, ((z • A) ^ n) v = (z * lambda) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply]
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, hv, smul_smul]
        rw [map_smul, ih]
        simp only [smul_smul]
        congr 1
        ring
  let ev : ContinuousOperator H →L[ℂ] H :=
    (ContinuousLinearMap.apply ℂ H) v
  have hop :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • A)).map ev ev.continuous
  have hscalar :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * lambda)).smul_const v
  rw [Complex.exp_eq_exp_ℂ]
  apply HasSum.unique hop
  apply hscalar.congr
  intro s
  apply Finset.sum_congr rfl
  intro n _hn
  simp [ev, hpow n, mul_smul]
end
end QEC.Semantics
end

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
    (hamiltonian : Operator K)
    (hX : Commute hamiltonian logical.x)
    (hZ : Commute hamiltonian logical.z)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) :
    (logical.physicalGibbsState hamiltonian hZ hhamiltonian beta).toOperator =
      ((ThermalEncoding.gibbsPartitionFunction beta
        (logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian) : ℂ)⁻¹) •
        (NormedSpace.exp
          ((-beta : ℂ) • LinearMap.toContinuousLinearMap hamiltonian)).toLinearMap := by
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K
  letI : Nonempty (Fin (Module.finrank ℂ logical.AuxiliarySpace)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  letI : Nonempty
      (Fin 2 × Fin (Module.finrank ℂ logical.AuxiliarySpace)) := inferInstance
  let b := logical.physicalHamiltonianEigenbasis hamiltonian hZ hhamiltonian
  let energy := logical.physicalHamiltonianEnergies hamiltonian hZ hhamiltonian
  apply Module.Basis.ext b.toBasis
  intro i
  change
    (ThermalEncoding.spectralGibbsDensity b energy beta).toOperator (b i) = _
  rw [ThermalEncoding.spectralGibbsDensity_apply_basis]
  change _ =
    ((ThermalEncoding.gibbsPartitionFunction beta energy : ℂ)⁻¹) •
      (NormedSpace.exp
        ((-beta : ℂ) • LinearMap.toContinuousLinearMap hamiltonian) (b i))
  have heigen : (LinearMap.toContinuousLinearMap hamiltonian) (b i) =
      (energy i : ℂ) • b i := by
    change hamiltonian (b i) = (energy i : ℂ) • b i
    exact logical.physicalHamiltonianEigenbasis_apply
      hamiltonian hX hZ hhamiltonian i
  rw [continuousOperator_exp_smul_apply_eigenvector _ _ _ _ heigen]
  simp only [smul_smul]
  congr 1
  rw [ThermalEncoding.gibbsProbability]
  have hexp : Complex.exp ((-beta : ℂ) * (energy i : ℂ)) =
      (Real.exp (-beta * energy i) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hexp]
  have hreal :
      Real.exp (-beta * energy i) /
          ThermalEncoding.gibbsPartitionFunction beta energy =
        (ThermalEncoding.gibbsPartitionFunction beta energy)⁻¹ *
          Real.exp (-beta * energy i) := by
    field_simp [ThermalEncoding.gibbsPartitionFunction_pos beta energy |>.ne']
  exact_mod_cast hreal
end ThermalEncoding.PauliLikePair
end QEC.Semantics
