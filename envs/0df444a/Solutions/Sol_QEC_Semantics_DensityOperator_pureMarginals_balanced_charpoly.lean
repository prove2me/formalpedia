-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.pureMarginals_balanced_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:27.815455+00:00
-- url     : https://prove2.me/submissions/78329aa9-d997-4d49-a4bd-944b6fa65785

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_pureDensity_toMatrix
import Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_pureDensity_toMatrix
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
theorem _root_.solution {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (rightMarginal (pureDensity psi hpsi)).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (leftMarginal (pureDensity psi hpsi)).toOperator.charpoly := by
  let bH := stdOrthonormalBasis Complex H
  let bK := stdOrthonormalBasis Complex K
  let C := coefficientMatrix bH bK psi
  have hright := rightMarginal_pureDensity_toMatrix bH bK psi hpsi
  have hleft := leftMarginal_pureDensity_toMatrix bH bK psi hpsi
  change LinearMap.toMatrix bH.toBasis bH.toBasis
      (rightMarginal (pureDensity psi hpsi)).toOperator = C * C.conjTranspose at hright
  change LinearMap.toMatrix bK.toBasis bK.toBasis
      (leftMarginal (pureDensity psi hpsi)).toOperator =
        (C.conjTranspose * C).transpose at hleft
  calc
    (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (rightMarginal (pureDensity psi hpsi)).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (C * C.conjTranspose).charpoly := by
          congr 1
          rw [← LinearMap.charpoly_toMatrix
            (rightMarginal (pureDensity psi hpsi)).toOperator bH.toBasis, hright]
    _ = (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (C.conjTranspose * C).charpoly := by
          simpa using Matrix.charpoly_mul_comm' C C.conjTranspose
    _ = (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (leftMarginal (pureDensity psi hpsi)).toOperator.charpoly := by
          congr 1
          rw [← LinearMap.charpoly_toMatrix
            (leftMarginal (pureDensity psi hpsi)).toOperator bK.toBasis, hleft,
            Matrix.charpoly_transpose]
end QEC.Semantics.DensityOperator
