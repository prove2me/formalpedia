-- Prove2me | solution 1 for QEC.Semantics.krausOperatorOfChoiVector_inner_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:23.795308+00:00
-- url     : https://prove2.me/submissions/433bfffc-9bb9-41d1-97f6-b643d8d44eae

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_toMatrix
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
theorem _root_.solution {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p) = v (i, p) := by
  have hmatrix := congrFun (congrFun
    (krausOperatorOfChoiVector_toMatrix bH bK v) p) i
  rw [LinearMap.toMatrix_apply] at hmatrix
  have hrepr :
      bK.repr ((krausOperatorOfChoiVector bH bK v) (bH i)) p =
        star (v (i, p)) := by
    simpa [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply] using hmatrix
  calc
    inner Complex ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p)
        = star (inner Complex (bK p) ((krausOperatorOfChoiVector bH bK v) (bH i))) := by
          exact (inner_conj_symm ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p)).symm
    _ = star (bK.repr ((krausOperatorOfChoiVector bH bK v) (bH i)) p) := by
          rw [OrthonormalBasis.repr_apply_apply]
    _ = v (i, p) := by
          simp [hrepr]
end QEC.Semantics
