-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.continuous_sumSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:31.011808+00:00
-- url     : https://prove2.me/submissions/363e8c93-4410-40ab-97a2-b2d59763a5e6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
import Theorems.Thm_PositivityTheory_ThKF0_Grow_foldr_mem

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
omit [AddCommGroup X] [IsTopologicalAddGroup X]
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) : Continuous (sumSq dd L Θ) :=
  continuous_list_sum L fun l _ => (ENNReal.continuous_pow 2).comp (hS _ (foldr_mem hd l h)).enorm
end PositivityTheory.ThKF0.Grow
