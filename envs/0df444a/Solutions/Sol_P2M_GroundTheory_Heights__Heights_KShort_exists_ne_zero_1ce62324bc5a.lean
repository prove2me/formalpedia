-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:23.182876+00:00
-- url     : https://prove2.me/submissions/c33853e7-d9f1-476b-a341-dac456e9098c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] : ∃ v ∈ L, v ≠ 0 := by
  by_contra h
  push Not at h
  have hbot : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact h
  rw [IsZLattice.span_top] at hbot
  have : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ∈ (⊥ : Submodule ℝ _) := by
    rw [← hbot]; trivial
  rw [Submodule.mem_bot] at this
  have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) this
  simp at this
end GroundTheory.Heights₂.Heights.KShort
