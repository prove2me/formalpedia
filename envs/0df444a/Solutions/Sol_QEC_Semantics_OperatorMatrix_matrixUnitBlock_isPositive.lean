-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.matrixUnitBlock_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:17.895339+00:00
-- url     : https://prove2.me/submissions/efb9aeba-dc18-4f59-b731-efcb996de904

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_adjoint
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.OperatorMatrix
theorem _root_.solution (b : OrthonormalBasis (Fin n) Complex H) :
    IsPositive (matrixUnitBlock b) := by
  classical
  constructor
  · intro i j
    change matrixUnit b j i = LinearMap.adjoint (matrixUnit b i j)
    rw [matrixUnit_adjoint]
  · intro x
    let coeff : Fin n → Complex := fun i => inner Complex (b i) (x i)
    have hQuadratic :
        (∑ i : Fin n, ∑ j : Fin n,
          inner Complex ((matrixUnitBlock b) i j (x j)) (x i)) =
          (∑ i : Fin n, coeff i) * star (∑ i : Fin n, coeff i) := by
      calc
        (∑ i : Fin n, ∑ j : Fin n,
            inner Complex ((matrixUnitBlock b) i j (x j)) (x i))
            = ∑ i : Fin n, ∑ j : Fin n, coeff i * star (coeff j) := by
              simp [matrixUnitBlock, matrixUnit, coeff]
        _ = (∑ i : Fin n, coeff i) * (∑ j : Fin n, star (coeff j)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _hi
              simp [Finset.mul_sum]
        _ = (∑ i : Fin n, coeff i) * star (∑ i : Fin n, coeff i) := by
              rw [star_sum]
    rw [hQuadratic]
    simpa [Complex.mul_conj, Complex.normSq_apply] using
      Complex.normSq_nonneg (∑ i : Fin n, coeff i)
end QEC.Semantics.OperatorMatrix
