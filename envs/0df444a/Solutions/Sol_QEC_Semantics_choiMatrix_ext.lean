-- Prove2me | solution 1 for QEC.Semantics.choiMatrix_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:13.475122+00:00
-- url     : https://prove2.me/submissions/cc50e282-b299-499e-9ec4-12f945bcc372

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_expansion
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
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution {n : Nat} {βK : Type*} [Fintype βK]
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K)
    (h : choiMatrix Φ bH bK = choiMatrix Ψ bH bK) :
    Φ = Ψ := by
  classical
  have hUnit : ∀ i j : Fin n,
      Φ (OperatorMatrix.matrixUnit bH i j) =
        Ψ (OperatorMatrix.matrixUnit bH i j) := by
    intro i j
    apply (Module.Basis.ext bK.toBasis)
    intro q
    change Φ (OperatorMatrix.matrixUnit bH i j) (bK q) =
      Ψ (OperatorMatrix.matrixUnit bH i j) (bK q)
    apply (ext_iff_inner_right Complex).2
    intro v
    rw [← OrthonormalBasis.sum_repr' bK v]
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro p _hp
    have hentry :
        inner Complex (Φ (OperatorMatrix.matrixUnit bH i j) (bK q)) (bK p) =
          inner Complex (Ψ (OperatorMatrix.matrixUnit bH i j) (bK q)) (bK p) := by
      have hentry := congrFun (congrFun h (i, p)) (j, q)
      simpa [choiMatrix, OperatorMatrix.scalarMatrix, OperatorMatrix.map,
        OperatorMatrix.matrixUnitBlock] using hentry
    rw [hentry]
  apply LinearMap.ext
  intro A
  calc
    Φ A = Φ (∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • OperatorMatrix.matrixUnit bH i j) := by
      rw [← OperatorMatrix.matrixUnit_expansion bH A]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • Φ (OperatorMatrix.matrixUnit bH i j) := by
      simp
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • Ψ (OperatorMatrix.matrixUnit bH i j) := by
      simp [hUnit]
    _ = Ψ (∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • OperatorMatrix.matrixUnit bH i j) := by
      simp
    _ = Ψ A := by
      rw [← OperatorMatrix.matrixUnit_expansion bH A]
end QEC.Semantics
