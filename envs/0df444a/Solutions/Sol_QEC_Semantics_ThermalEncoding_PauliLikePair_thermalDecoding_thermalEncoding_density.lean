-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:24.031206+00:00
-- url     : https://prove2.me/submissions/2cb5b095-3add-4573-86d2-7d1d0ae7a456

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalDecoding_thermalEncoding
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (sigma : DensityOperator P.AuxiliarySpace) (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalDecoding.mapDensity (P.thermalEncoding sigma |>.mapDensity eta) = eta := by
  apply DensityOperator.ext_toOperator
  exact P.thermalDecoding_thermalEncoding sigma eta.toOperator
end QEC.Semantics.ThermalEncoding.PauliLikePair
