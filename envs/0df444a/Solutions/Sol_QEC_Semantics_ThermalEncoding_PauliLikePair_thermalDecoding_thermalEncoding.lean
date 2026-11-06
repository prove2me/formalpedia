-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:47.262985+00:00
-- url     : https://prove2.me/submissions/fee1551e-23fe-4c80-8a80-a53c1b11c8b5

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_partialTraceRightRaw_prepareRight

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
set_option maxRecDepth 4096
namespace QEC.Semantics.ThermalEncoding.PauliLikePair
theorem _root_.solution
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalDecoding (P.thermalEncoding sigma A) = A := by
  change partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
    (P.factorization.symm.conjOperator
      (P.factorization.conjOperator
        (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma A))) = A
  rw [P.factorization.symm_conjOperator_conjOperator,
    partialTraceRightRaw_prepareRight]
end QEC.Semantics.ThermalEncoding.PauliLikePair
