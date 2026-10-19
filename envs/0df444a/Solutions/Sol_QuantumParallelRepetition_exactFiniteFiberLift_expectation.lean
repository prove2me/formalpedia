-- Prove2me | solution 1 for QuantumParallelRepetition.exactFiniteFiberLift_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/be517b49-262d-4139-8539-c1ad45167ec6

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactFiniteFiberLift_groupedMass

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
namespace QuantumParallelRepetition
theorem _root_.solution
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (value : T → ℝ) :
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T, target point * value point := by
  calc
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T,
        groupedMass projection
          (exactFiniteFiberLift projection original target) point *
            value point :=
      (finiteGroupedExpectation_eq_atom_sum projection
        (exactFiniteFiberLift projection original target)
        value).symm
    _ = ∑ point : T, target point * value point := by
      simp_rw [exactFiniteFiberLift_groupedMass
        projection original target supported]
end QuantumParallelRepetition
