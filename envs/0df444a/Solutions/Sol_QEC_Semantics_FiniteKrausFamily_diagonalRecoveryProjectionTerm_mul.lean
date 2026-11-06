-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionTerm_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:27.496821+00:00
-- url     : https://prove2.me/submissions/7a666e84-e790-4d51-be81-bb7f30144256

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_projector_comp
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_cross
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
theorem _root_.solution
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a b : ι) :
    (((LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
      ((LinearMap.adjoint (diagonalRecoveryOperator C F lambda b)).comp
        (diagonalRecoveryOperator C F lambda b))) =
      if a = b then
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)
      else 0 := by
  classical
  let Ra := diagonalRecoveryOperator C F lambda a
  let Rb := diagonalRecoveryOperator C F lambda b
  have hcross := diagonalRecoveryOperator_cross
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a b
  by_cases hab : a = b
  · subst b
    by_cases ha0 : lambda a = 0
    · unfold diagonalRecoveryOperator
      rw [if_pos ha0]
      simp
    · have hcross_aa :
          Ra.comp (LinearMap.adjoint Ra) = C.projector := by
        simpa [Ra, ha0] using hcross
      have hP := diagonalRecoveryOperator_projector_comp F C lambda a
      rw [if_pos rfl]
      ext x
      calc
        (((LinearMap.adjoint Ra).comp Ra).comp
          ((LinearMap.adjoint Ra).comp Ra)) x
            = (LinearMap.adjoint Ra)
                ((Ra.comp (LinearMap.adjoint Ra)) (Ra x)) := by
                simp [LinearMap.comp_apply]
        _ = (LinearMap.adjoint Ra) (C.projector (Ra x)) := by
                rw [hcross_aa]
        _ = (LinearMap.adjoint Ra) (Ra x) := by
                have hPx := congrArg (fun A : Operator H => A x) hP
                simpa [Ra, LinearMap.comp_apply] using
                  congrArg (fun y : H => (LinearMap.adjoint Ra) y) hPx
        _ = ((LinearMap.adjoint Ra).comp Ra) x := by
                simp [LinearMap.comp_apply]
  · have hcross_ab :
        Ra.comp (LinearMap.adjoint Rb) = 0 := by
      simpa [Ra, Rb, hab] using hcross
    rw [if_neg hab]
    ext x
    calc
      (((LinearMap.adjoint Ra).comp Ra).comp
        ((LinearMap.adjoint Rb).comp Rb)) x
          = (LinearMap.adjoint Ra)
              ((Ra.comp (LinearMap.adjoint Rb)) (Rb x)) := by
              simp [LinearMap.comp_apply]
      _ = 0 := by
              rw [hcross_ab]
              simp
end QEC.Semantics.FiniteKrausFamily
