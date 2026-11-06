-- Prove2me | solution 1 for QEC.Semantics.Davies.one_sub_adjoint_square_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:08:06.019914+00:00
-- url     : https://prove2.me/submissions/9f28abe6-3cbe-4686-9805-a4c82a7efc2f

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_TraceBound
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
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
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (A : Operator V) (hA : operatorNorm A ≤ 1) :
    (1 - LinearMap.adjoint A * A).IsPositive := by
  constructor
  · exact (LinearMap.isPositive_one : (1 : Operator V).IsPositive).isSymmetric.sub
      (LinearMap.isSymmetric_adjoint_mul_self A)
  · intro x
    change 0 ≤ (inner ℂ (x - LinearMap.adjoint A (A x)) x).re
    rw [inner_sub_left, Complex.sub_re, LinearMap.adjoint_inner_left]
    rw [show (inner ℂ x x).re = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x,
      show (inner ℂ (A x) (A x)).re = ‖A x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) (A x)]
    have hnorm : ‖A x‖ ≤ ‖x‖ := by
      have h := (LinearMap.toContinuousLinearMap A).le_opNorm x
      exact h.trans (by simpa [operatorNorm] using mul_le_mul_of_nonneg_right hA (norm_nonneg x))
    nlinarith [norm_nonneg x, norm_nonneg (A x)]
end QEC.Semantics.Davies
