-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.lintegral_sumSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:05.984349+00:00
-- url     : https://prove2.me/submissions/caa65c0c-60d8-4e18-b9f9-32e7b82d9fc9

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
theorem _root_.solution [MeasurableSpace X] [BorelSpace X] (μ : Measure X) {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ)
    {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) :
    ∫⁻ y, sumSq dd L Θ y ∂μ = (L.map fun l => ∫⁻ y, ‖l.foldr dd Θ y‖ₑ ^ 2 ∂μ).sum := by
  induction L with
  | nil => simp [sumSq]
  | cons l L ih =>
    rw [List.map_cons, List.sum_cons, ← ih,
      ← lintegral_add_left ((hS _ (foldr_mem hd l h)).measurable.enorm.pow_const 2)]
    rfl
end PositivityTheory.ThKF0.Grow
