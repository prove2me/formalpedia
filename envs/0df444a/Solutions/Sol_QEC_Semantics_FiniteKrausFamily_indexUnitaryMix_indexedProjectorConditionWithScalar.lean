-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexUnitaryMix_indexedProjectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:56.465912+00:00
-- url     : https://prove2.me/submissions/a0afa69f-8f3e-4e33-aab3-b88dae5f5de3

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
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
    (U : Matrix.unitaryGroup ι Complex)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    IndexedKnillLaflammeProjectorConditionWithScalar (E.indexUnitaryMix U) C
      (fun a b : ι =>
        ((star (U : Matrix ι ι Complex)) * (Matrix.of fun i j => scalar i j) *
          (U : Matrix ι ι Complex)) a b) := by
  classical
  intro a b
  ext x
  calc
    (((C.projector.comp
      ((LinearMap.adjoint ((E.indexUnitaryMix U).operator a)).comp
        ((E.indexUnitaryMix U).operator b))).comp C.projector) x)
        = (∑ j : ι, ∑ i : ι,
            ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a)) •
              (((C.projector.comp
                ((LinearMap.adjoint (E.operator i)).comp (E.operator j))).comp
                  C.projector) x)) := by
              simp [indexUnitaryMix, indexMix, map_sum, map_smulₛₗ,
                LinearMap.comp_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
    _ = (∑ j : ι, ∑ i : ι,
            ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a)) •
              ((scalar i j • C.projector) x)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              apply Finset.sum_congr rfl
              intro i _hi
              rw [hKL i j]
    _ = (((∑ j : ι, ∑ i : ι,
            scalar i j * ((U : Matrix ι ι Complex) j b *
              star ((U : Matrix ι ι Complex) i a))) • C.projector) x) := by
              simp [Finset.sum_smul, smul_smul, mul_comm]
    _ = ((((star (U : Matrix ι ι Complex)) * (Matrix.of fun i j => scalar i j) *
          (U : Matrix ι ι Complex)) a b) • C.projector) x := by
              have hmatrix :
                  (((star (U : Matrix ι ι Complex)) *
                    (Matrix.of fun i j => scalar i j) *
                    (U : Matrix ι ι Complex)) a b) =
                    ∑ j : ι, ∑ i : ι,
                      scalar i j * ((U : Matrix ι ι Complex) j b *
                        star ((U : Matrix ι ι Complex) i a)) := by
                calc
                  (((star (U : Matrix ι ι Complex)) *
                    (Matrix.of fun i j => scalar i j) *
                    (U : Matrix ι ι Complex)) a b)
                      = ∑ j : ι,
                          (∑ i : ι,
                            star ((U : Matrix ι ι Complex) i a) * scalar i j) *
                            (U : Matrix ι ι Complex) j b := by
                            simp [Matrix.mul_apply]
                  _ = ∑ j : ι, ∑ i : ι,
                      (star ((U : Matrix ι ι Complex) i a) * scalar i j) *
                        (U : Matrix ι ι Complex) j b := by
                        apply Finset.sum_congr rfl
                        intro j _hj
                        rw [Finset.sum_mul]
                  _ = ∑ j : ι, ∑ i : ι,
                      scalar i j * ((U : Matrix ι ι Complex) j b *
                        star ((U : Matrix ι ι Complex) i a)) := by
                        apply Finset.sum_congr rfl
                        intro j _hj
                        apply Finset.sum_congr rfl
                        intro i _hi
                        ring
              rw [hmatrix]
end QEC.Semantics.FiniteKrausFamily
