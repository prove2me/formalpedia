-- Prove2me | solution 2 for PositivityTheory.ThKF0.Grow.foldr_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:43.40335+00:00
-- url     : https://prove2.me/submissions/a2334216-9fef-4d45-8f32-0d6693e3f65f

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
omit [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution {S : Set (X → ℂ)} {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (l : List W) {Θ : X → ℂ}
    (h : Θ ∈ S) : l.foldr dd Θ ∈ S := by
  induction l with
  | nil => exact h
  | cons w l ih => exact hd w _ ih
end PositivityTheory.ThKF0.Grow
