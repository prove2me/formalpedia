-- Prove2me | solution 1 for SoficGroups.KunSharpThresholdCut.integrableOn_crossingIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/cc015e0f-fcf7-4fc9-8eec-d883a0d5a4f9

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
    IntegrableOn ((Ico a b).indicator (fun _ => (1 : ℝ)))
      (Ioo c d) := by
  exact (integrableOn_const (μ := volume)
    (C := (1 : ℝ)) (s := Ioo c d)
    (by simp [Real.volume_Ioo])).indicator measurableSet_Ico
end SoficGroups.KunSharpThresholdCut
