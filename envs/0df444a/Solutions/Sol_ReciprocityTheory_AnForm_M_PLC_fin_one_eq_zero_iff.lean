-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.fin_one_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:57.060338+00:00
-- url     : https://prove2.me/submissions/6dcb5534-6284-4554-8e48-4c5cdb203edc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLC
theorem _root_.solution (y : Fin 1 → ℂ) : y = 0 ↔ y 0 = 0 := by
  constructor
  · rintro rfl; rfl
  · intro h; funext i; fin_cases i; exact h
end ReciprocityTheory.AnForm.M.PLC
