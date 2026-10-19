-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGreedyCeilingHorizon_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/2283f24c-d070-4378-bd68-be5bffd9ec23

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (small : d ≤ τ / 2) :
    ⌈d * (n : ℝ) / τ⌉₊ ≤ n := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ threshold).mpr
  have actual := mul_le_mul_of_nonneg_right small
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith
end QuantumParallelRepetition
