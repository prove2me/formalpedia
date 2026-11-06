-- Prove2me | solution 1 for QEC.Semantics.finiteLindbladEvolution_traceNorm_sub_le_time_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:09:58.495734+00:00
-- url     : https://prove2.me/submissions/460bab65-a826-4270-994e-25acac562af2

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_CompletelyPositive_intervalIntegral
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_apply_le_of_isSymmetric
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionContinuous_integral
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_hasDerivAt_finiteLindbladEvolutionReal
import Theorems.Thm_QEC_Semantics_intervalIntegral_comp_comm
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
private theorem clbtTraceNorm_intervalIntegral_bound
    (f : ℝ → ContinuousOperator H) (t C : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 t)
    (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.uIoc 0 t,
      traceNorm ((f s).toLinearMap) ≤ C) :
    traceNorm
        ((continuousOperatorToCLBTTraceNormed (H := H)
          (∫ s in (0 : ℝ)..t, f s) : CLBTTraceNormedOperator H)) ≤
      t * C := by
  change ‖continuousOperatorToCLBTTraceNormed (H := H)
    (∫ s in (0 : ℝ)..t, f s)‖ ≤ t * C
  rw [← intervalIntegral_comp_comm
    (continuousOperatorToCLBTTraceNormed (H := H)) f 0 t hf]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s =>
    continuousOperatorToCLBTTraceNormed (H := H) (f s)) (C := C) (by
      intro s hs
      change traceNorm ((f s).toLinearMap) ≤ C
      exact hbound s hs)
  simpa [abs_of_nonneg ht, mul_comm] using h
private theorem lindbladJumpTerm_isSymmetric
    (J A : Operator H) (hA : A.IsSymmetric) :
    (lindbladJumpTerm J A).IsSymmetric := by
  let K : Operator H := LinearMap.adjoint J * J
  have hK : K.IsSymmetric := by
    exact LinearMap.isSymmetric_adjoint_comp_self J
  have hgain : (J * A * LinearMap.adjoint J).IsSymmetric := by
    exact hA.conj_adjoint J
  have hloss : (K * A + A * K).IsSymmetric := by
    intro x y
    simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_left,
      inner_add_right]
    rw [hK, hA, hA, hK]
    ac_rfl
  rw [lindbladJumpTerm_apply]
  apply hgain.sub
  apply hloss.smul
  rw [map_inv₀]
  congr 1
  change star (2 : ℂ) = 2
  norm_num
private theorem lindbladDissipator_isSymmetric [Fintype ι]
    (J : ι → Operator H) (A : Operator H) (hA : A.IsSymmetric) :
    (lindbladDissipator J A).IsSymmetric := by
  rw [lindbladDissipator_apply]
  exact LinearMap.isSymmetric_sum Finset.univ fun i _ =>
    lindbladJumpTerm_isSymmetric (J i) A hA
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
theorem _root_.solution [Fintype ι]
    [Nontrivial H]
    (hamiltonian : Operator H) (J : ι → Operator H)
    (hhamiltonian : hamiltonian.IsSymmetric)
    (A : Operator H) (hA : A.IsSymmetric)
    (hcomm : Commute hamiltonian A)
    (t : ℝ) (ht : 0 ≤ t) :
    traceNorm (finiteLindbladEvolutionLinearMap hamiltonian J t A - A) ≤
      t * traceNorm (lindbladDissipator J A) := by
  let G := asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)
  let Ac : ContinuousOperator H := LinearMap.toContinuousLinearMap A
  let D : Operator H := lindbladDissipator J A
  have hgenerator : finiteLindbladGenerator hamiltonian J A = D := by
    change hamiltonianCommutator hamiltonian A + lindbladDissipator J A = D
    have hzero : hamiltonianCommutator hamiltonian A = 0 := by
      rw [hamiltonianCommutator_apply, hcomm.eq, sub_self, smul_zero]
    rw [hzero, zero_add]
  have hDsym : D.IsSymmetric := by
    exact lindbladDissipator_isSymmetric J A hA
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => finiteLindbladEvolutionContinuous hamiltonian J (r : ℂ))
      (finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) s :=
    fun s => hasDerivAt_finiteLindbladEvolutionReal hamiltonian J s
  have hE : Continuous (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ)) :=
    continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hprod : Continuous (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) *
        asContinuousSuperoperator (finiteLindbladGenerator hamiltonian J)) :=
    hE.mul continuous_const
  have hfint : IntervalIntegrable
      (fun s : ℝ =>
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac))
      MeasureTheory.volume 0 t := by
    have hconst : Continuous (fun _ : ℝ => Ac) := continuous_const
    simpa [G] using (hprod.clm_apply hconst).intervalIntegrable 0 t
  have hintegral := finiteLindbladEvolutionContinuous_integral hamiltonian J t
  have happly :
      (∫ s in (0 : ℝ)..t,
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac)) =
        finiteLindbladEvolutionContinuous hamiltonian J (t : ℂ) Ac - Ac := by
    have heval := intervalIntegral_comp_comm
      ((ContinuousLinearMap.apply ℂ (ContinuousOperator H) Ac).restrictScalars ℝ)
      (fun s : ℝ =>
        finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) * G)
      0 t (by simpa [G] using hprod.intervalIntegrable 0 t)
    rw [hintegral] at heval
    simpa [G, Ac, sub_apply] using heval
  have hbound := clbtTraceNorm_intervalIntegral_bound
    (fun s : ℝ =>
      finiteLindbladEvolutionContinuous hamiltonian J (s : ℂ) (G Ac))
    t (traceNorm D) hfint ht (by
      intro s hs
      have hsnonneg : 0 ≤ s := by
        have hs' : s ∈ Set.Ioc 0 t := by simpa [Set.uIoc_of_le ht] using hs
        exact hs'.1.le
      have hcontract :=
        (finiteLindbladEvolutionChannel hamiltonian J hhamiltonian s hsnonneg)
          |>.traceNorm_apply_le_of_isSymmetric D hDsym
      have hinput : G Ac = LinearMap.toContinuousLinearMap D := by
        change LinearMap.toContinuousLinearMap
          (finiteLindbladGenerator hamiltonian J A) =
            LinearMap.toContinuousLinearMap D
        rw [hgenerator]
      rw [hinput]
      change traceNorm
        (finiteLindbladEvolutionLinearMap hamiltonian J s D) ≤ traceNorm D
      exact hcontract)
  rw [happly] at hbound
  change traceNorm
      (finiteLindbladEvolutionLinearMap hamiltonian J t A - A) ≤
    t * traceNorm D
  exact hbound
end QEC.Semantics
