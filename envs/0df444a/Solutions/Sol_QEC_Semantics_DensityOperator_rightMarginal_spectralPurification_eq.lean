-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.rightMarginal_spectralPurification_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:21:17.622129+00:00
-- url     : https://prove2.me/submissions/50e1249d-811c-437f-afed-9c9795665d0d

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification

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
theorem _root_.solution (rho : DensityOperator H) :
    rightMarginal (spectralPurification rho) = rho :=
  ext_toOperator (rightMarginal_spectralPurification rho)
end QEC.Semantics.DensityOperator
