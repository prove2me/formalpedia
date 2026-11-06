-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:58.821246+00:00
-- url     : https://prove2.me/submissions/55e6712d-5bee-4d34-a5e3-6f0a4c1c1136

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_adjoint
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_error_projector
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
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    let S : Operator H :=
      ∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)
    (1 - S).comp
      ((F.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0 := by
  classical
  intro S
  have hS_adjoint :
      LinearMap.adjoint S = S := by
    exact diagonalRecoveryProjectionSum_adjoint F C lambda
  have hResidualAdjoint : LinearMap.adjoint (1 - S : Operator H) = 1 - S := by
    rw [map_sub, LinearMap.adjoint_one, hS_adjoint]
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hleft_kill :
      (1 - S).comp (F.inducedMap rho.toOperator) = 0 := by
    calc
      (1 - S).comp (F.inducedMap rho.toOperator)
          = ∑ i : ι, (1 - S).comp
              (((F.operator i).comp C.projector).comp
                (rho.toOperator.comp (LinearMap.adjoint (F.operator i)))) := by
              ext x
              simp [FiniteKrausFamily.inducedMap_apply, Finset.sum_apply,
                LinearMap.comp_apply, S, hPρ_apply]
      _ = 0 := by
              apply Finset.sum_eq_zero
              intro i _hi
              let B : Operator H := rho.toOperator.comp (LinearMap.adjoint (F.operator i))
              have hSi := diagonalRecoveryProjectionSum_error_projector
                (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL i
              have hkill :
                  (1 - S).comp ((F.operator i).comp C.projector) = 0 := by
                change (1 -
                    (∑ a : ι,
                      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
                        (diagonalRecoveryOperator C F lambda a))).comp
                    ((F.operator i).comp C.projector) = 0
                ext y
                have hy := congrArg (fun A : Operator H => A y) hSi
                simp [LinearMap.comp_apply] at hy ⊢
                exact sub_eq_zero.mpr hy.symm
              calc
                (1 - S).comp (((F.operator i).comp C.projector).comp B)
                    = ((1 - S).comp ((F.operator i).comp C.projector)).comp B := by
                    ext y
                    simp [B, LinearMap.comp_apply]
                _ = 0 := by
                    rw [hkill]
                    ext y
                    simp
  rw [hResidualAdjoint]
  ext x
  have hx := congrArg (fun A : Operator H => A ((1 - S) x)) hleft_kill
  simpa [LinearMap.comp_apply] using hx
end QEC.Semantics.FiniteKrausFamily
