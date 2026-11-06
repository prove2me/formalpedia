-- Prove2me | solution 1 for QEC.Semantics.choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:40:00.389991+00:00
-- url     : https://prove2.me/submissions/c495d8e7-ccf2-42ab-a6b2-7a58fb0c9911

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_adjoint_inner_basis
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
private theorem krausOperatorOfChoiVector_matrixUnit_apply_inner {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i j : Fin n) (p q : betaK) :
    inner Complex
      (((krausOperatorOfChoiVector bH bK v).comp
          ((OperatorMatrix.matrixUnit bH i j).comp
            (LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)))) (bK q))
      (bK p) =
      v (i, p) * star (v (j, q)) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [← LinearMap.adjoint_inner_right (𝕜 := Complex)
    (krausOperatorOfChoiVector bH bK v)
    ((OperatorMatrix.matrixUnit bH i j)
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK q)))
    (bK p)]
  rw [OperatorMatrix.matrixUnit_apply]
  rw [inner_smul_left]
  rw [krausOperatorOfChoiVector_adjoint_inner_basis bH bK v j q]
  rw [krausOperatorOfChoiVector_adjoint_inner_basis bH bK v i p]
  rw [mul_comm]
  rw [starRingEnd_apply]
namespace QuantumChannel
end QuantumChannel
end
end Semantics
end QEC
end

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution {m n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin m → (Fin n × betaK → Complex)) :
    choiMatrix ((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap) bH bK =
      ∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a)) := by
  classical
  ext ip jq
  rcases ip with ⟨i, p⟩
  rcases jq with ⟨j, q⟩
  change inner Complex
      (((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap
        (OperatorMatrix.matrixUnit bH i j)) (bK q)) (bK p) =
      (∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a))) (i, p) (j, q)
  calc
    inner Complex
        (((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap
          (OperatorMatrix.matrixUnit bH i j)) (bK q)) (bK p)
        = ∑ a : Fin m,
            inner Complex
              (((krausOperatorOfChoiVector bH bK (v a)).comp
                ((OperatorMatrix.matrixUnit bH i j).comp
                  (LinearMap.adjoint (krausOperatorOfChoiVector bH bK (v a))))) (bK q))
              (bK p) := by
          rw [FiniteKrausFamily.inducedMap_apply]
          simp only [finiteKrausFamilyOfChoiVectors, LinearMap.sum_apply, sum_inner]
    _ = ∑ a : Fin m, v a (i, p) * star (v a (j, q)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact krausOperatorOfChoiVector_matrixUnit_apply_inner bH bK (v a) i j p q
    _ = (∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a))) (i, p) (j, q) := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Matrix.vecMulVec_apply, Pi.star_apply]
end QEC.Semantics
