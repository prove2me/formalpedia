-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_rankOne_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:39.090271+00:00
-- url     : https://prove2.me/submissions/7ebae8da-edec-484d-acbb-15b64865c3ce

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator_apply_basis_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_comp_rankOne_comp_adjoint
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    (S : QuditSubsystem q) (rho : DensityOperator S.selectedSystem)
    (a b : Fin (Module.finrank Complex S.selectedSystem))
    (k l : S.complementSystem) :
    (S.replacementFactorizedKraus rho).inducedMap
      (InnerProductSpace.rankOne Complex
        (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
        (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap =
  if a = b then ∑ i : Fin (S.densityEnsembleSize rho),
        (InnerProductSpace.rankOne Complex
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] k)
          ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] l)).toLinearMap else 0 := by
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_prod_type]
  have hExpand :
      (∑ i : Fin (S.densityEnsembleSize rho),
        ∑ r : Fin (Module.finrank Complex S.selectedSystem),
          ((S.replacementFactorizedKraus rho).operator (i, r)).comp
            ((InnerProductSpace.rankOne Complex
              (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k)
              (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l)).toLinearMap.comp
                (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator (i, r))))) =
        ∑ i : Fin (S.densityEnsembleSize rho),
          ∑ r : Fin (Module.finrank Complex S.selectedSystem),
            (InnerProductSpace.rankOne Complex
              ((S.replacementFactorizedKraus rho).operator (i, r)
                (((stdOrthonormalBasis Complex S.selectedSystem) a) ⊗ₜ[Complex] k))
              ((S.replacementFactorizedKraus rho).operator (i, r)
                (((stdOrthonormalBasis Complex S.selectedSystem) b) ⊗ₜ[Complex] l))).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro r _
          exact S.comp_rankOne_comp_adjoint _ _ _
  rw [hExpand]
  simp_rw [S.replacementFactorizedKraus_operator_apply_basis_tmul]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single a]
    · simp
    · intro r _ hra
      have hne : r ≠ a := fun h => hra h
      rw [if_neg hne, if_neg hne]
      apply LinearMap.ext
      intro z
      change inner Complex (0 : S.factorizedSystem) z • (0 : S.factorizedSystem) = 0
      simp
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  · simp only [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro r _
    by_cases hra : r = a
    · subst r
      rw [if_pos rfl, if_neg hab]
      apply LinearMap.ext
      intro z
      change inner Complex (0 : S.factorizedSystem) z •
        ((S.densityEnsembleVectors rho i) ⊗ₜ[Complex] k) = 0
      simp
    · rw [if_neg hra]
      apply LinearMap.ext
      intro z
      change inner Complex
        (if r = b then (S.densityEnsembleVectors rho i) ⊗ₜ[Complex] l else 0) z •
          (0 : S.factorizedSystem) = 0
      simp
end QEC.Semantics.QuditSubsystem
