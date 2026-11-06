-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_branches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:22.307935+00:00
-- url     : https://prove2.me/submissions/e8b8c419-f023-49f3-bb18-e63f2de66e55

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_density_branch
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
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
theorem _root_.solution
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (hdiag_sum : (∑ i : ι, (lambda i : Complex)) • C.projector = C.projector)
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    (∑ a : ι, (diagonalRecoveryOperator C F lambda a).comp
      ((F.inducedMap rho.toOperator).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)))) =
      rho.toOperator := by
  classical
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hweight_rho :
      (∑ i : ι, (lambda i : Complex)) • rho.toOperator = rho.toOperator := by
    ext x
    have hx := congrArg (fun A : Operator H => A (rho.toOperator x)) hdiag_sum
    simpa [hPρ_apply x] using hx
  calc
    (∑ a : ι, (diagonalRecoveryOperator C F lambda a).comp
      ((F.inducedMap rho.toOperator).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))
        = ∑ a : ι, ∑ i : ι,
            (diagonalRecoveryOperator C F lambda a).comp
              ((F.operator i).comp
                (rho.toOperator.comp
                  ((LinearMap.adjoint (F.operator i)).comp
                    (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))) := by
            ext x
            simp [FiniteKrausFamily.inducedMap_apply, Finset.sum_apply]
    _ = ∑ a : ι, ∑ i : ι,
          if a = i then (lambda i : Complex) • rho.toOperator else 0 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro i _hi
            exact diagonalRecoveryOperator_density_branch
              (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL rho hρ a i
    _ = ∑ i : ι, (lambda i : Complex) • rho.toOperator := by
            ext x
            simp
    _ = rho.toOperator := by
            rw [← Finset.sum_smul]
            exact hweight_rho
end QEC.Semantics.FiniteKrausFamily
