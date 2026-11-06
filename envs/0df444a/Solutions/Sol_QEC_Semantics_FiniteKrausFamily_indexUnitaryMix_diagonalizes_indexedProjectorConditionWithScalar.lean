-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexUnitaryMix_diagonalizes_indexedProjectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:06.958196+00:00
-- url     : https://prove2.me/submissions/81ffb2aa-7570-4777-9c9c-480e599ed438

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexUnitaryMix_indexedProjectorConditionWithScalar
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
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hPSD : (Matrix.of fun i j => scalar i j).PosSemidef)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    ∃ U : Matrix.unitaryGroup ι Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar (E.indexUnitaryMix U) C
        (fun a b : ι =>
          Matrix.diagonal (fun i : ι =>
            (hPSD.1.eigenvalues i : Complex)) a b) ∧
      ∀ i : ι, 0 ≤ hPSD.1.eigenvalues i := by
  classical
  let A : Matrix ι ι Complex := Matrix.of fun i j => scalar i j
  let U : Matrix.unitaryGroup ι Complex := hPSD.1.eigenvectorUnitary
  refine ⟨U, ?_, Matrix.PosSemidef.eigenvalues_nonneg hPSD⟩
  have hmix := indexUnitaryMix_indexedProjectorConditionWithScalar
    (E := E) (C := C) (scalar := scalar) U hKL
  have hdiag :
      (star (U : Matrix ι ι Complex)) * A * (U : Matrix ι ι Complex) =
        Matrix.diagonal (fun i : ι => (hPSD.1.eigenvalues i : Complex)) := by
    have hspectral := hPSD.1.conjStarAlgAut_star_eigenvectorUnitary
    simpa [A, U, Unitary.conjStarAlgAut_apply, Function.comp_def] using hspectral
  intro a b
  simpa [A, hdiag] using hmix a b
end QEC.Semantics.FiniteKrausFamily
