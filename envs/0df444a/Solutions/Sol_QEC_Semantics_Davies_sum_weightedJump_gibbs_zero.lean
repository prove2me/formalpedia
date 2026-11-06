-- Prove2me | solution 1 for QEC.Semantics.Davies.sum_weightedJump_gibbs_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:23:55.812129+00:00
-- url     : https://prove2.me/submissions/ee3145aa-d7ee-456f-8d1d-007afef81ca5

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_gibbs_term
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_ext
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
theorem _root_.solution {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (β : ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (hA : ∀ a, (A a).IsSymmetric)
    (hDB : ∀ a w, rate a (negFrequency e w) = Real.exp (-β*w.val) * rate a w)
    (a : κ) :
    (∑ w : Frequency e, lindbladJumpTerm (weightedJump b e A rate (a,w))
      (spectralGibbsDensity b e β).toOperator) = 0 := by
  simp_rw [weightedJump_gibbs_term b e β A rate hn]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  let R := (spectralGibbsDensity b e β).toOperator
  let f := fun w : Frequency e => (rate a w : ℂ) •
    (R * LinearMap.adjoint (frequencyComponent b e (A a) w.val) * frequencyComponent b e (A a) w.val)
  change _ = ∑ w, f w
  rw [← (negFrequency e).sum_comp f]
  apply Finset.sum_congr rfl
  intro w _
  dsimp [f,R]
  rw [hDB]
  have hadj : ∀ ω, LinearMap.adjoint (frequencyComponent b e (A a) ω) =
      frequencyComponent b e (A a) (-ω) := by
    intro ω
    rw [frequencyComponent_adjoint, (hA a).adjoint_eq]
  simp only [negFrequency, Equiv.coe_fn_mk, hadj, neg_neg]
  simp only [← Complex.ofReal_mul, mul_comm]
  apply entry_ext b
  intro i j
  simp only [entry_smul, entry_real_smul, Complex.ofReal_mul]
end QEC.Semantics.Davies
