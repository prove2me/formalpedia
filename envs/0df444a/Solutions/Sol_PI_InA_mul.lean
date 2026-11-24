-- Prove2me | solution 1 for PI.InA.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:32.284043+00:00
-- url     : https://prove2.me/submissions/676df4d6-af7c-43d7-b03b-49c35d4cbe89

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
open PI
open Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI
namespace InA
theorem _root_.solution {X Y : Mx k r} (hX : InA k r X) (hY : InA k r Y) : InA k r (X * Y) := by
  constructor
  · intro a i hai
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : a.val ≤ l.val
    · rw [hY.1 a l hl, mul_zero]
    · have hl' : l.val < r := by have := a.2; omega
      have : l = eI k r ⟨l.val, hl'⟩ := rfl
      rw [this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]
  · intro i j h1 h2 h3
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : r ≤ l.val
    · rw [hY.2 l j h1 h2 hl, mul_zero]
    · have hl' : l.val < r := by omega
      have : l = eI k r ⟨l.val, hl'⟩ := rfl
      rw [this, hX.1 ⟨l.val, hl'⟩ i (by simp only; omega), zero_mul]
end InA
end PI
