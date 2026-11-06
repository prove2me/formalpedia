-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.operatorNorm_le_one_of_positive_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:35.062611+00:00
-- url     : https://prove2.me/submissions/22dd2d9f-5c4a-403f-ba42-4410174a2623

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution
    (A : Operator H) (hA : LinearMap.IsPositive A)
    (hIA : LinearMap.IsPositive (1 - A)) :
    ‖LinearMap.toContinuousLinearMap A‖ ≤ 1 := by
  let T := LinearMap.toContinuousLinearMap A
  have hTc : T.IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  calc
    ‖LinearMap.toContinuousLinearMap A‖ =
        ⨆ x : H, |T.rayleighQuotient x| := by
          exact T.norm_eq_iSup_rayleighQuotient hTc.isSymmetric
    _ ≤ 1 := by
      apply ciSup_le
      intro x
      by_cases hx : x = 0
      · simp [hx]
      have hdenom : 0 < ‖x‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hlower : 0 ≤ T.reApplyInnerSelf x :=
        hTc.re_inner_nonneg_left x
      have hupper : T.reApplyInnerSelf x ≤ ‖x‖ ^ 2 := by
        have h := hIA.re_inner_nonneg_left x
        change 0 ≤
          Complex.re (inner Complex (((1 - A) : Operator H) x) x) at h
        have happly : (((1 - A) : Operator H) x) = x - A x := by
          rfl
        rw [happly, inner_sub_left, Complex.sub_re] at h
        have hnorm : (inner Complex x x).re = ‖x‖ ^ 2 := by
          exact inner_self_eq_norm_sq (𝕜 := Complex) x
        rw [hnorm] at h
        change (inner Complex (A x) x).re ≤ ‖x‖ ^ 2
        exact sub_nonneg.mp h
      have hquotient :
          T.rayleighQuotient x =
            T.reApplyInnerSelf x / ‖x‖ ^ 2 := rfl
      have hq_nonneg : 0 ≤ T.rayleighQuotient x := by
        rw [hquotient]
        exact div_nonneg hlower hdenom.le
      have hq_le : T.rayleighQuotient x ≤ (1 : Real) := by
        rw [hquotient]
        exact (div_le_one hdenom).mpr hupper
      simpa [abs_of_nonneg hq_nonneg] using hq_le
end QEC.Semantics.ThermalEncoding
