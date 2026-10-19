-- Prove2me | solution 1 for QuantumParallelRepetition.postselection_log_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/6585b17a-5906-491c-9e0b-9ef223025d4d

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
    {θ p : ℝ} (hθ : 0 < θ) (hθp : θ ≤ p) :
    Real.log (1 / p) ≤ Real.log (1 / θ) := by
  have hp : 0 < p := lt_of_lt_of_le hθ hθp
  have hinv : 1 / p ≤ 1 / θ := by
    exact one_div_le_one_div_of_le hθ hθp
  exact Real.log_le_log (by positivity : 0 < 1 / p) hinv
end QuantumParallelRepetition
