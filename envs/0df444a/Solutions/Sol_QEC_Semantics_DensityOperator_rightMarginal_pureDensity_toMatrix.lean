-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.rightMarginal_pureDensity_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:56.238109+00:00
-- url     : https://prove2.me/submissions/86151729-0739-4d80-a4a9-ee67d5f45002

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_pureDensity_toOperator

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
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bH.toBasis bH.toBasis
      (rightMarginal (pureDensity psi hpsi)).toOperator =
      coefficientMatrix bH bK psi * (coefficientMatrix bH bK psi).conjTranspose := by
  rw [rightMarginal_pureDensity_toOperator bK psi hpsi]
  rw [LinearMap.toMatrix_comp bH.toBasis bK.toBasis bH.toBasis,
    LinearMap.toMatrix_adjoint bK bH]
  rfl
end QEC.Semantics.DensityOperator
