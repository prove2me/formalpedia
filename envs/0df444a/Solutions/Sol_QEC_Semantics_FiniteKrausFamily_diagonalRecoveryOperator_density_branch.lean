-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_density_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:42:25.590191+00:00
-- url     : https://prove2.me/submissions/9b3dbe0f-331c-4260-b209-52d9b80851ec

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branch
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branch_adjoint
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_comp_projector_eq_self
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
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho)
    (a i : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        ((F.operator i).comp
          (rho.toOperator.comp
            ((LinearMap.adjoint (F.operator i)).comp
              (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))) =
      if a = i then (lambda i : Complex) • rho.toOperator else 0 := by
  classical
  let R := diagonalRecoveryOperator C F lambda a
  have hleft := diagonalRecoveryOperator_branch
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i
  have hright := diagonalRecoveryOperator_branch_adjoint
    (F := F) (C := C) (lambda := lambda) hlambda_nonneg hKL a i
  have hPρ := DensityOperator.supportedOn_projector_comp_eq_self C rho hρ
  have hρP := DensityOperator.supportedOn_comp_projector_eq_self C rho hρ
  have hPρ_apply : ∀ x : H, C.projector (rho.toOperator x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hPρ
  have hρP_apply : ∀ x : H, rho.toOperator (C.projector x) = rho.toOperator x := by
    intro x
    simpa [LinearMap.comp_apply] using
      congrArg (fun A : Operator H => A x) hρP
  have hinsert :
      R.comp
          ((F.operator i).comp
            (rho.toOperator.comp
              ((LinearMap.adjoint (F.operator i)).comp
                (LinearMap.adjoint R)))) =
        (R.comp ((F.operator i).comp C.projector)).comp
          (rho.toOperator.comp
            ((C.projector.comp (LinearMap.adjoint (F.operator i))).comp
              (LinearMap.adjoint R))) := by
    ext x
    simp [R, LinearMap.comp_apply, hPρ_apply, hρP_apply]
  by_cases hai : a = i
  · subst a
    have hsquareR : Real.sqrt (lambda i) * Real.sqrt (lambda i) = lambda i := by
      simpa [sq] using Real.sq_sqrt (hlambda_nonneg i)
    rw [hinsert]
    rw [hleft, hright]
    ext x
    simp [LinearMap.comp_apply, hPρ_apply, hρP_apply, smul_smul]
    exact congrArg (fun r : ℝ => (r : Complex) • rho.toOperator x) hsquareR
  · rw [hinsert]
    rw [hleft, hright]
    simp [hai]
end QEC.Semantics.FiniteKrausFamily
