-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.PauliLikePair.symm_conjOperator_eq_tensorAuxiliaryOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:55.912048+00:00
-- url     : https://prove2.me/submissions/2e0fc65c-6d4f-46a5-b924-c63624d6f2dc

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorAuxiliaryOperator

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
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z) :
    P.factorization.symm.conjOperator A = P.tensorAuxiliaryOperator A hZ := by
  rw [← P.factorization.symm_conjOperator_conjOperator
    (P.tensorAuxiliaryOperator A hZ), P.conj_tensorAuxiliaryOperator A hX hZ]
end QEC.Semantics.ThermalEncoding.PauliLikePair
