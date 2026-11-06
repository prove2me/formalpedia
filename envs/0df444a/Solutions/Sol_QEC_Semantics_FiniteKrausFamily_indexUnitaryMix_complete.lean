-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexUnitaryMix_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:28.984531+00:00
-- url     : https://prove2.me/submissions/5d38f807-8beb-4459-aa3d-ccdd64689ea3

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_unitaryGroup_sum_star_col_mul_col_smul
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution (E : FiniteKrausFamily ι H H)
    (U : Matrix.unitaryGroup ι Complex) (hE : E.Complete) :
    (E.indexUnitaryMix U).Complete := by
  classical
  unfold Complete indexUnitaryMix
  rw [← hE]
  ext x
  calc
    (∑ a : ι,
      (LinearMap.adjoint ((E.indexMix (U : Matrix ι ι Complex)).operator a)).comp
        ((E.indexMix (U : Matrix ι ι Complex)).operator a)) x
        = ∑ a : ι, ∑ i : ι, ∑ j : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) •
              (LinearMap.adjoint (E.operator i) (E.operator j x)) := by
              simp [indexMix, map_sum, map_smulₛₗ, Finset.sum_apply,
                Finset.smul_sum, smul_smul]
    _ = ∑ i : ι, LinearMap.adjoint (E.operator i) (E.operator i x) := by
              simpa using
                (unitaryGroup_sum_star_col_mul_col_smul U
                  (fun i j => LinearMap.adjoint (E.operator i) (E.operator j x)))
    _ = (∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i)) x := by
              simp [Finset.sum_apply]
end QEC.Semantics.FiniteKrausFamily
