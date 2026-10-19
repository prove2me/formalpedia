-- Prove2me | solution 1 for QuantumParallelRepetition.divisorStopping_nat_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/c4e188e7-1740-48d8-b5b3-15e1170f02d1

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
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    n < 2 * (n / q) * q := by
  have hT : 0 < n / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa using hqn
  have hnext : n < (n / q + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (n / q))
  have hfactor : n / q + 1 ≤ 2 * (n / q) := by
    omega
  exact hnext.trans_le (Nat.mul_le_mul_right q hfactor)
end QuantumParallelRepetition
