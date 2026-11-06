-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.ket_comp_bra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:47:02.8061+00:00
-- url     : https://prove2.me/submissions/39ae0205-5745-4392-ad50-f6fdae9fc3d9

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
omit [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (psi : H) :
    (ket psi).comp (bra psi) = (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  rfl
end QEC.Semantics.DensityOperator
