-- Prove2me | solution 1 for QuantumParallelRepetition.exactFiniteFiberLift_groupedMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/78f627f0-bd6f-4340-a0e9-1ba1d0c2e66b

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
omit [Fintype T]
namespace QuantumParallelRepetition
theorem _root_.solution
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (exactFiniteFiberLift projection original target) point =
        target point := by
  classical
  change
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
        target point
  calc
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        target point * original outcome /
          groupedMass projection original point := by
          apply Finset.sum_congr rfl
          intro outcome member
          have same : projection outcome = point :=
            (Finset.mem_filter.mp member).2
          simp [exactFiniteFiberLift, same]
    _ = target point * groupedMass projection original point /
          groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
          rfl
    _ = target point := by
          by_cases empty : groupedMass projection original point = 0
          · simp [empty, supported point empty]
          · field_simp
end QuantumParallelRepetition
