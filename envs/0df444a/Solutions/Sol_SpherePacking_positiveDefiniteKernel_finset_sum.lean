-- Prove2me | solution 1 for SpherePacking.positiveDefiniteKernel_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/33dc4375-4f39-4f93-92a4-a610f5739f47

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
namespace SpherePacking
theorem _root_.solution {α ι : Type*}
    (I : Finset ι) (K : ι → α → α → ℝ)
    (hK : ∀ i ∈ I, PositiveDefiniteKernel (K i)) :
    PositiveDefiniteKernel (fun x y => ∑ i ∈ I, K i x y) := by
  intro C w
  calc
    0 ≤ ∑ i ∈ I, ∑ x ∈ C, ∑ y ∈ C,
        w x * w y * K i x y := by
      exact Finset.sum_nonneg fun i hi => hK i hi C w
    _ = ∑ x ∈ C, ∑ i ∈ I, ∑ y ∈ C,
        w x * w y * K i x y := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C, ∑ i ∈ I,
        w x * w y * K i x y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C,
        w x * w y * (∑ i ∈ I, K i x y) := by
      simp_rw [Finset.mul_sum]
end SpherePacking
