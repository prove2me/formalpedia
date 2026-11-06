-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.exists_recovery_of_sameSpaceKnillLaflammeCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:48:54.683985+00:00
-- url     : https://prove2.me/submissions/d836fe68-f1a2-4d6e-8224-6d07a0a7166d

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctable_id_of_carrier_eq_bot
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexUnitaryMix_complete
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexUnitaryMix_inducedMap_eq
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_diagonalProjectorConditionWithScalar
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_correctedBy_iff_correctable_toQuantumChannel
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
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C E recovery := by
  classical
  by_cases hCbot : C.carrier = ⊥
  · refine ⟨QuantumChannel.id H, hE, ?_⟩
    exact (E.correctedBy_iff_correctable_toQuantumChannel hE C (QuantumChannel.id H)).2
      (correctable_id_of_carrier_eq_bot E C hE hCbot)
  · rcases sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
      E C hE hCbot hKL with
      ⟨scalar, hscalarKL, hPSD, _hdiag, _hherm⟩
    rcases indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
      (E := E) (C := C) (scalar := scalar) hPSD hscalarKL with
      ⟨U, hdiagKL, hlambda_nonneg⟩
    let F : FiniteKrausFamily ι H H := E.indexUnitaryMix U
    let lambda : ι → ℝ := fun i => hPSD.1.eigenvalues i
    have hF : F.Complete := by
      simpa [F] using indexUnitaryMix_complete E U hE
    have hdiagKL' :
        IndexedKnillLaflammeProjectorConditionWithScalar F C
          (fun a b : ι =>
            Matrix.diagonal (fun i : ι => (lambda i : Complex)) a b) := by
      simpa [F, lambda] using hdiagKL
    have hlambda_nonneg' : ∀ i : ι, 0 ≤ lambda i := by
      simpa [lambda] using hlambda_nonneg
    rcases exists_recovery_of_diagonalProjectorConditionWithScalar
      F C hF (lambda := lambda) hlambda_nonneg' hdiagKL' with
      ⟨recovery, hrecF⟩
    refine ⟨recovery, hE, ?_⟩
    intro rho hρ
    have hcorrectF := hrecF.2 rho hρ
    have hmap := indexUnitaryMix_inducedMap_eq E U rho.toOperator
    simpa [F, hmap] using hcorrectF
end QEC.Semantics.FiniteKrausFamily
