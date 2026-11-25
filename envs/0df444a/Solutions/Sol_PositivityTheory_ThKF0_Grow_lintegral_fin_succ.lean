-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.lintegral_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:38.448403+00:00
-- url     : https://prove2.me/submissions/867bf752-7aab-4133-a062-24b6628df8fd

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
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution {D : ℕ} (G : (Fin (D + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ t, G t = ∫⁻ s : ℝ, ∫⁻ t : Fin D → ℝ, G (Fin.cons s t) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℝ) 0).symm
  rw [← hp.lintegral_comp hG, Measure.volume_eq_prod,
    lintegral_prod (fun a => G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℝ) 0).symm a))
      (hG.comp (MeasurableEquiv.measurable _)).aemeasurable]
  refine lintegral_congr fun s => lintegral_congr fun t => congrArg G ?_
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
end PositivityTheory.ThKF0.Grow
