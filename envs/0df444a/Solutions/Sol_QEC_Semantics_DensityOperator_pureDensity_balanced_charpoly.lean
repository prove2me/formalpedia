-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.pureDensity_balanced_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:23.520688+00:00
-- url     : https://prove2.me/submissions/1d66ce44-11a1-41dd-b985-9fcdc35e3897

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_ket_comp_bra
import Theorems.Thm_QEC_Semantics_DensityOperator_bra_comp_ket
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) * (pureDensity psi hpsi).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (Polynomial.X - 1) := by
  let bH := stdOrthonormalBasis Complex H
  let bC : OrthonormalBasis Unit Complex Complex := OrthonormalBasis.singleton Unit Complex
  let A := ket psi
  let B := bra psi
  let C := LinearMap.toMatrix bC.toBasis bH.toBasis A
  let D := LinearMap.toMatrix bH.toBasis bC.toBasis B
  have hCD : (C * D).charpoly = (pureDensity psi hpsi).toOperator.charpoly := by
    rw [← LinearMap.toMatrix_comp bH.toBasis bC.toBasis bH.toBasis]
    change (LinearMap.toMatrix bH.toBasis bH.toBasis (A.comp B)).charpoly = _
    rw [ket_comp_bra]
    exact LinearMap.charpoly_toMatrix _ bH.toBasis
  have hDC : (D * C).charpoly = Polynomial.X - 1 := by
    rw [← LinearMap.toMatrix_comp bC.toBasis bH.toBasis bC.toBasis]
    change (LinearMap.toMatrix bC.toBasis bC.toBasis (B.comp A)).charpoly = _
    rw [bra_comp_ket psi hpsi, LinearMap.charpoly_toMatrix, LinearMap.charpoly_one]
    simp [Module.finrank_self]
  have hmatrix := Matrix.charpoly_mul_comm' C D
  simpa [hCD, hDC, Fintype.card_unique] using hmatrix
end QEC.Semantics.DensityOperator
