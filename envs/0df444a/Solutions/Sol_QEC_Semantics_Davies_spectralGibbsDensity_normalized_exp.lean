-- Prove2me | solution 1 for QEC.Semantics.Davies.spectralGibbsDensity_normalized_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:52.765389+00:00
-- url     : https://prove2.me/submissions/a9c7a164-4718-40e5-b1ec-a1723e241a46

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
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
attribute [local simp] QEC.Semantics.Davies.entry_diagonal_mul
attribute [local simp] QEC.Semantics.Davies.entry_frequencyComponent
attribute [local simp] QEC.Semantics.Davies.entry_mul_diagonal
attribute [local simp] QEC.Semantics.Davies.frequencyComponent_zero
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
namespace QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private theorem exp_apply_eigenvector
    (A : ContinuousOperator V) (v : V) (lambda z : ℂ)
    (hv : A v = lambda • v) :
    NormedSpace.exp (z • A) v = Complex.exp (z * lambda) • v := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hpow : ∀ n : ℕ, ((z • A) ^ n) v = (z * lambda) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_apply_eq_comp]
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, hv, smul_smul]
        rw [map_smul, ih]
        simp only [smul_smul]
        congr 1
        ring
  let ev : ContinuousOperator V →L[ℂ] V := (ContinuousLinearMap.apply ℂ V) v
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • A)).map ev ev.continuous
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z * lambda)).smul_const v
  rw [Complex.exp_eq_exp_ℂ]
  apply HasSum.unique hop
  apply hscalar.congr
  intro s
  apply Finset.sum_congr rfl
  intro n _
  simp [ev, hpow n, mul_smul]
end
end QEC.Semantics.Davies
end

set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (H : Operator V)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (heigen : ∀ i, H (b i) = (e i : ℂ) • b i) (β : ℝ) :
    (spectralGibbsDensity b e β).toOperator =
      ((gibbsPartitionFunction β e : ℂ)⁻¹) •
        (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H)).toLinearMap := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  apply b.toBasis.ext
  intro i
  change (spectralGibbsDensity b e β).toOperator (b i) = _
  rw [spectralGibbsDensity_apply_basis]
  change _ = ((gibbsPartitionFunction β e : ℂ)⁻¹) •
    (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap H) (b i))
  rw [exp_apply_eigenvector _ _ _ _ (heigen i)]
  simp only [smul_smul]
  congr 1
  rw [gibbsProbability]
  have hexp : Complex.exp ((-β : ℂ) * (e i : ℂ)) = (Real.exp (-β * e i) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hexp]
  push_cast
  ring
end QEC.Semantics.Davies
