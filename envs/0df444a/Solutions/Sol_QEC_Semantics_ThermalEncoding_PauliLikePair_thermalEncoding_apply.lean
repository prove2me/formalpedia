-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:27.21622+00:00
-- url     : https://prove2.me/submissions/da9dfa56-9f42-4353-983f-33d6f18e65a2

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply

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
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalEncoding sigma A =
      P.factorization.conjOperator (TensorProduct.map A sigma.toOperator) := by
  change P.factorization.conjOperator
    (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma A) = _
  rw [prepareRight_apply]
end QEC.Semantics.ThermalEncoding.PauliLikePair
