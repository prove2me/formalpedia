-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGreedyCard_lt_of_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/77e47844-6e1e-4a2c-8794-8d767fc5802a

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
    (k n : ℕ) (τ d : ℝ)
    (below : k < ⌈d * (n : ℝ) / τ⌉₊) :
    (k : ℝ) < d * (n : ℝ) / τ :=
  Nat.lt_ceil.mp below
end QuantumParallelRepetition
