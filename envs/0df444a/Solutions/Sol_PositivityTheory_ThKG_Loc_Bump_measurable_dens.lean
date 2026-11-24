-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.measurable_dens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:44.044058+00:00
-- url     : https://prove2.me/submissions/4d82b624-61b6-45b9-8f5e-8b23b4ae4831

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution : Measurable (dens : (ι → ℂ) → ℝ≥0) := by
  refine Measurable.subtype_mk ?_
  fun_prop
end PositivityTheory.ThKG.Loc.Bump
