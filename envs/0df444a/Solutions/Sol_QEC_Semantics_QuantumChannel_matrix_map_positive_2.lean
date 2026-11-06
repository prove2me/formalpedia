-- Prove2me | solution 2 for QEC.Semantics.QuantumChannel.matrix_map_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:18.585646+00:00
-- url     : https://prove2.me/submissions/2f0b009d-9a08-4da1-8b9a-7291f3ffc653

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.QuantumChannel
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Φ : QuantumChannel H K) (n : Nat) (M : OperatorMatrix n H)
    (hM : OperatorMatrix.IsPositive M) :
    OperatorMatrix.IsPositive (OperatorMatrix.map Φ.toLinearMap M) :=
  Φ.completely_positive n M hM
end QEC.Semantics.QuantumChannel
