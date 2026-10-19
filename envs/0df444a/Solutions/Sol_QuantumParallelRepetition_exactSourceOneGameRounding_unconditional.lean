-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceOneGameRounding_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/faea44c7-d2ac-4ccc-b86c-51f8b2760c1a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSourceOneGameRounding_uniform

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    ExactSourceOneGameRounding G := by
  obtain ⟨K, constant, round⟩ :=
    unconditionalSourceOneGameRounding_uniform
  refine ⟨K, le_trans (by norm_num : (0 : ℝ) ≤ 1) constant, ?_⟩
  exact round G
end QuantumParallelRepetition
