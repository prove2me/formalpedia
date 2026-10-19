-- Prove2me | solution 1 for QuantumParallelRepetition.sourceRate_mul_lt_divisorStopping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/4c4c95a0-77aa-478c-99a9-3e3616da35c0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_divisorStopping_nat_bound

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
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    {η : ℝ} (hη : 0 < η) :
    (η / (4 * (q : ℝ))) * (n : ℝ) <
      η * ((n / q : ℕ) : ℝ) := by
  have hcast :
      (n : ℝ) < 2 * ((n / q : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast divisorStopping_nat_bound hq hqn
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hT : 0 < ((n / q : ℕ) : ℝ) := by
    exact_mod_cast ((Nat.le_div_iff_mul_le hq).2 (by simpa using hqn) :
      1 ≤ n / q)
  have hrate : 0 < η / (4 * (q : ℝ)) := by positivity
  calc
    (η / (4 * (q : ℝ))) * (n : ℝ) <
        (η / (4 * (q : ℝ))) *
          (2 * ((n / q : ℕ) : ℝ) * (q : ℝ)) :=
      mul_lt_mul_of_pos_left hcast hrate
    _ = η * ((n / q : ℕ) : ℝ) / 2 := by
      field_simp
      ; ring
    _ < η * ((n / q : ℕ) : ℝ) := by
      have hpositive : 0 < η * ((n / q : ℕ) : ℝ) :=
        mul_pos hη hT
      linarith
end QuantumParallelRepetition
