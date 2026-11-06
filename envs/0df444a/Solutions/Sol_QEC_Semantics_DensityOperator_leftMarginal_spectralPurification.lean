-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.leftMarginal_spectralPurification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:49.915498+00:00
-- url     : https://prove2.me/submissions/5a01a8b2-a313-4011-bb81-5abe98c7b136

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_conj_spectralPurification

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
    (leftMarginal (spectralPurification rho)).toOperator = rho.toOperator := by
  rw [leftMarginal, tensorSwap_conj_spectralPurification]
  exact rightMarginal_spectralPurification rho
end QEC.Semantics.DensityOperator
