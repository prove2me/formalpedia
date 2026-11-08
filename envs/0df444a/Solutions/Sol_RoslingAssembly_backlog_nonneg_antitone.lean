-- Prove2me | solution 1 for RoslingAssembly.backlog_nonneg_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:59:44.033079+00:00
-- url     : https://prove2.me/submissions/99f48446-0356-47c6-9102-4f236dc1793b

import Mathlib
import Definitions.Def_RoslingAssembly_backlogG

open MeasureTheory

open RoslingAssembly in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hμac : μ ≪ volume) (hμi : Integrable (fun x => x) μ)
    (hlam : 0 < ∫ x, x ∂μ) (m : ℕ) :
    (∀ y : ℝ, 0 ≤ backlogG μ m y) ∧ Antitone (backlogG μ m) := by
  have hcoord : ∀ j : Fin (m + 1),
      Integrable (fun x : Fin (m + 1) → ℝ => x j) (Measure.pi fun _ : Fin (m + 1) => μ) :=
    fun j => (measurePreserving_eval (μ := fun _ : Fin (m + 1) => μ) j).integrable_comp_of_integrable hμi
  have hint : ∀ y : ℝ, Integrable (fun x : Fin (m + 1) → ℝ => max 0 (∑ j, x j - y))
      (Measure.pi fun _ : Fin (m + 1) => μ) := by
    intro y
    have h1 : Integrable (fun x : Fin (m + 1) → ℝ => ∑ j, x j - y)
        (Measure.pi fun _ : Fin (m + 1) => μ) :=
      (integrable_finsetSum _ (fun j _ => hcoord j)).sub (integrable_const y)
    exact h1.pos_part.congr (Filter.Eventually.of_forall fun x => max_comm _ _)
  refine ⟨fun y => ?_, fun y1 y2 h => ?_⟩
  · unfold backlogG
    exact integral_nonneg (fun x => le_max_left _ _)
  · unfold backlogG
    exact integral_mono (hint y2) (hint y1)
      (fun x => max_le_max le_rfl (sub_le_sub_left h _))
