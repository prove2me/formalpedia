-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.tensorSwap_conj_spectralPurification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:24.272945+00:00
-- url     : https://prove2.me/submissions/e4de7999-3f6a-4f01-ba99-fbc3af4fd00a

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_spectralPurificationVector
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



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
    (tensorSwap H H).conjDensity (spectralPurification rho) = spectralPurification rho := by
  apply ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, spectralPurification,
    pureDensity_toOperator, QuditSubsystem.conjOperator_rankOne,
    tensorSwap_spectralPurificationVector]
end QEC.Semantics.DensityOperator
