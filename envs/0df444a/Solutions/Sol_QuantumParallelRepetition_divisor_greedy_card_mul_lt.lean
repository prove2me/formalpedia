-- Prove2me | solution 1 for QuantumParallelRepetition.divisor_greedy_card_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/e827856d-6e17-489a-9207-e969b09516f3

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {n q : ℕ} (hq : 0 < q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    D.card * q < n := by
  have hmul : D.card * q < (n / q) * q :=
    Nat.mul_lt_mul_of_pos_right hD hq
  exact hmul.trans_le (Nat.div_mul_le_self n q)
end QuantumParallelRepetition
