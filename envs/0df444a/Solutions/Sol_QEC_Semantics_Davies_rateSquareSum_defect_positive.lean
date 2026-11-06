-- Prove2me | solution 1 for QEC.Semantics.Davies.rateSquareSum_defect_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:25:52.326956+00:00
-- url     : https://prove2.me/submissions/aa1dd56d-a0f0-4f3a-9590-88e67926d8af

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Pinching
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Theorems.Thm_QEC_Semantics_CompletelyPositive_add
import Theorems.Thm_QEC_Semantics_Davies_entry_diagonal_mul
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_entry_mul_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_zero
import Theorems.Thm_QEC_Semantics_Davies_one_sub_frequency_squareSum_positive
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
open scoped BigOperators ComplexOrder
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Davies
theorem _root_.solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : operatorNorm A ≤ 1) (rate : Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hu : ∀ w, rate w ≤ hmax) :
    ((hmax : ℂ) • (1 : Operator V) - rateSquareSum b e A rate).IsPositive := by
  have he : (hmax : ℂ) • (1 : Operator V) - rateSquareSum b e A rate =
      (hmax : ℂ) • (1-squareSum (fun w : Frequency e => frequencyComponent b e A w.val)) +
      ∑ w : Frequency e, ((hmax-rate w : ℝ) : ℂ) •
        (LinearMap.adjoint (frequencyComponent b e A w.val) * frequencyComponent b e A w.val) := by
    simp only [rateSquareSum, squareSum, Complex.ofReal_sub, sub_smul,
      Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub]
    module
  rw [he]
  apply LinearMap.IsPositive.add
  · exact (one_sub_frequency_squareSum_positive b e A hA).smul_of_nonneg (by exact_mod_cast hm)
  · apply LinearMap.isPositive_sum
    intro w _
    exact (LinearMap.isPositive_adjoint_comp_self _).smul_of_nonneg
      (by exact_mod_cast sub_nonneg.mpr (hu w))
end QEC.Semantics.Davies
