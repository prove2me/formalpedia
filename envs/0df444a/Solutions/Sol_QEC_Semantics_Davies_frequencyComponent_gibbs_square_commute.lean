-- Prove2me | solution 1 for QEC.Semantics.Davies.frequencyComponent_gibbs_square_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:12:42.035777+00:00
-- url     : https://prove2.me/submissions/d1844dd7-078c-45de-91c5-a295f3328adc

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_gibbs
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_adjoint
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



set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β ω : ℝ) (A : Operator V) :
    Commute (LinearMap.adjoint (frequencyComponent b e A ω) * frequencyComponent b e A ω)
      (spectralGibbsDensity b e β).toOperator := by
  let C := frequencyComponent b e A ω
  let R := (spectralGibbsDensity b e β).toOperator
  have hc : C * R = (Real.exp (-β*ω) : ℂ) • (R*C) := frequencyComponent_gibbs b e β ω A
  have hd : LinearMap.adjoint C * R = (Real.exp (-β*(-ω)) : ℂ) • (R*LinearMap.adjoint C) := by
    dsimp [C,R]
    rw [frequencyComponent_adjoint]
    exact frequencyComponent_gibbs b e β (-ω) (LinearMap.adjoint A)
  have hq : (Real.exp (-β*ω) : ℂ) * (Real.exp (-β*(-ω)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have he : -β*ω + -β*(-ω) = 0 := by ring
    rw [he]; simp
  change LinearMap.adjoint C * C * R = R * (LinearMap.adjoint C*C)
  calc
    _ = LinearMap.adjoint C * (C*R) := mul_assoc _ _ _
    _ = (Real.exp (-β*ω) : ℂ) • ((LinearMap.adjoint C*R)*C) := by rw [hc]; simp [mul_assoc]
    _ = ((Real.exp (-β*ω) : ℂ) * (Real.exp (-β*(-ω)) : ℂ)) •
        (R*(LinearMap.adjoint C*C)) := by rw [hd]; simp [smul_smul, mul_assoc]
    _ = _ := by rw [hq]; simp
end QEC.Semantics.Davies
