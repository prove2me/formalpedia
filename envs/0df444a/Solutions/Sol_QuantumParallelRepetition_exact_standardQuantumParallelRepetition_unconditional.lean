-- Prove2me | solution 1 for QuantumParallelRepetition.exact_standardQuantumParallelRepetition_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/5af32dca-6871-4011-9491-804c6d99506d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exact_standardQuantumParallelRepetition_of_source_rounding
import Theorems.Thm_QuantumParallelRepetition_exactSourceOneGameRounding_unconditional

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
    StandardQuantumParallelRepetition G :=
  exact_standardQuantumParallelRepetition_of_source_rounding G
    (exactSourceOneGameRounding_unconditional G)
end QuantumParallelRepetition
