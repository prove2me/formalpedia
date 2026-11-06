-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.matrixUnit_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:19.030642+00:00
-- url     : https://prove2.me/submissions/5d5187a7-934c-4c6c-a855-6e3162208d27

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
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
theorem _root_.solution
    (b : OrthonormalBasis (Fin n) Complex H) (A : Operator H) :
    A = ∑ i : Fin n, ∑ j : Fin n,
      (b.repr (A (b j)) i) • matrixUnit b i j := by
  classical
  apply (Module.Basis.ext b.toBasis)
  intro k
  change A (b k) = (∑ i : Fin n, ∑ j : Fin n,
    (b.repr (A (b j)) i) • matrixUnit b i j) (b k)
  have hinner : ∀ j : Fin n, inner Complex (b j) (b k) = if j = k then 1 else 0 := by
    intro j
    exact (orthonormal_iff_ite.mp b.orthonormal) j k
  rw [← OrthonormalBasis.sum_repr' b (A (b k))]
  simp [matrixUnit_apply, hinner, OrthonormalBasis.repr_apply_apply]
end QEC.Semantics.OperatorMatrix
