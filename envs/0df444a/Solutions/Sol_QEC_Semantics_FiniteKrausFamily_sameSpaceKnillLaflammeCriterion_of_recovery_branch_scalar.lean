-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_of_recovery_branch_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:36.50946+00:00
-- url     : https://prove2.me/submissions/89f40f62-386c-4900-b1e2-ae3035322d85

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
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
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (branchScalar : κ → ι → Complex)
    (hbranch : ∀ r i (x : H), x ∈ C.carrier →
      R r (E.operator i x) = branchScalar r i • x) :
    E.sameSpaceKnillLaflammeCriterion C := by
  classical
  rw [E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C]
  refine ⟨fun i j => ∑ r : κ, star (branchScalar r i) * branchScalar r j, ?_⟩
  intro i j x hx y hy
  calc
    inner Complex (E.operator i x) (E.operator j y)
        = inner Complex (((∑ r : κ, (LinearMap.adjoint (R r)).comp (R r))
            (E.operator i x))) (E.operator j y) := by
          rw [hR_complete]
          simp
    _ = ∑ r : κ,
          inner Complex (((LinearMap.adjoint (R r)).comp (R r)) (E.operator i x))
            (E.operator j y) := by
          simp [Finset.sum_apply]
    _ = ∑ r : κ, inner Complex (R r (E.operator i x)) (R r (E.operator j y)) := by
          apply Finset.sum_congr rfl
          intro r _hr
          simpa [LinearMap.comp_apply] using
            (LinearMap.adjoint_inner_left (𝕜 := Complex) (R r)
              (E.operator j y) (R r (E.operator i x)))
    _ = ∑ r : κ, (star (branchScalar r i) * branchScalar r j) *
          inner Complex x y := by
          apply Finset.sum_congr rfl
          intro r _hr
          rw [hbranch r i x hx, hbranch r j y hy]
          simp [mul_left_comm, mul_comm]
    _ = (∑ r : κ, star (branchScalar r i) * branchScalar r j) *
          inner Complex x y := by
          rw [Finset.sum_mul]
end QEC.Semantics.FiniteKrausFamily
