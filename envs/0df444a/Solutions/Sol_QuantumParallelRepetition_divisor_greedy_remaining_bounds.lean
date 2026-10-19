-- Prove2me | solution 1 for QuantumParallelRepetition.divisor_greedy_remaining_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/d529b841-4c51-4fde-a7e2-f96a18f47516

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_divisor_greedy_card_mul_lt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    {n q : ℕ} (hq : 2 ≤ q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    0 < (Finset.univ \ D).card ∧
      n ≤ 2 * (Finset.univ \ D).card ∧
      D.card * q ≤ 2 * (Finset.univ \ D).card := by
  classical
  have hqpos : 0 < q := by omega
  have hdq : D.card * q < n :=
    divisor_greedy_card_mul_lt hqpos hD
  have htwo : D.card * 2 < n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left D.card hq) hdq
  have hcard : (Finset.univ \ D).card + D.card = n := by
    simpa using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ D))
  omega
end QuantumParallelRepetition
