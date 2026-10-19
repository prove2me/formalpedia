-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.setIntegral_crossingIndicator_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/d66e3eec-f636-4d8b-a111-26e3ba8b53c5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
namespace SoficGroups.KunSharpThresholdCut
theorem _root_.solution
    (a b c d : ℝ) :
    (∫ t in Ioo c d,
      (Ico a b).indicator (fun _ => (1 : ℝ)) t) ≤ |b - a| := by
  calc
    (∫ t in Ioo c d,
        (Ico a b).indicator (fun _ => (1 : ℝ)) t) =
        (volume.restrict (Ioo c d)).real (Ico a b) := by
          exact integral_indicator_one (μ := volume.restrict (Ioo c d))
            measurableSet_Ico
    _ = volume.real (Ico a b ∩ Ioo c d) :=
      measureReal_restrict_apply measurableSet_Ico
    _ ≤ volume.real (Ico a b) :=
      measureReal_mono inter_subset_left
        (by simp [Real.volume_Ico])
    _ = max (b - a) 0 := Real.volume_real_Ico
    _ ≤ |b - a| := max_le (le_abs_self _) (abs_nonneg _)
end SoficGroups.KunSharpThresholdCut
