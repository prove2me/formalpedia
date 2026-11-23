-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLC.two_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:32.849131+00:00
-- url     : https://prove2.me/submissions/b1df7fc7-4f5b-441c-bf42-33f9e53d406c

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
theorem _root_.solution : (2 : WithTop ℕ∞) ≤ ∞ := by exact WithTop.coe_le_coe.mpr le_top
end ReciprocityTheory.AnForm.M.PLC
