-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.leftMarginal_spectralPurification_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:55.088573+00:00
-- url     : https://prove2.me/submissions/d73e02e2-f595-476f-aa2a-e625d47668a5

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_spectralPurification

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
    leftMarginal (spectralPurification rho) = rho :=
  ext_toOperator (leftMarginal_spectralPurification rho)
end QEC.Semantics.DensityOperator
