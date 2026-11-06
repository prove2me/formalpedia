-- Prove2me | solution 1 for QEC.Semantics.Davies.weightedJump_gibbs_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:15:19.449235+00:00
-- url     : https://prove2.me/submissions/045a1e1a-1a7e-4e34-8c0a-bac8afaff0e5

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_gibbs
import Theorems.Thm_QEC_Semantics_Davies_weightedJump_term
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_gibbs_square_commute
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
    (hn : ∀ a w, 0 ≤ rate a w) (a : κ) (w : Frequency e) :
    lindbladJumpTerm (weightedJump b e A rate (a,w)) (spectralGibbsDensity b e β).toOperator =
      (rate a w * Real.exp (-β*w.val) : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * frequencyComponent b e (A a) w.val *
          LinearMap.adjoint (frequencyComponent b e (A a) w.val)) -
      (rate a w : ℂ) •
        ((spectralGibbsDensity b e β).toOperator * LinearMap.adjoint (frequencyComponent b e (A a) w.val) *
          frequencyComponent b e (A a) w.val) := by
  rw [weightedJump_term b e A rate hn, lindbladJumpTerm_apply,
    frequencyComponent_gibbs b e β w.val (A a),
    (frequencyComponent_gibbs_square_commute b e β w.val (A a)).eq]
  simp only [smul_mul_assoc, ← mul_assoc, smul_sub, smul_add, smul_smul,
    Complex.ofReal_mul]
  module
end QEC.Semantics.Davies
