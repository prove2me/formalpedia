-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.matrix_map_positive
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:55:04.726161+00:00
-- url     : https://prove2.me/submissions/f18468a3-fdae-418b-a6a8-bb70543a0e5b

-- ID: 1cba259e-b8cd-4cc5-aa23-d13a5a038f5c | NAME: QEC.Semantics.QuantumChannel.matrix_map_positive | 未本地编译验证
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

theorem solution (Φ : QuantumChannel H K) (n : Nat) (M : OperatorMatrix n H)
    (hM : OperatorMatrix.IsPositive M) :
    OperatorMatrix.IsPositive (OperatorMatrix.map Φ.toLinearMap M) := by
  exact Φ.completely_positive n M hM
