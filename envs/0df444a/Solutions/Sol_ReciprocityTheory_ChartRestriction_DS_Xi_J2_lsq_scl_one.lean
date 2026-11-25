-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.lsq_scl_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:29.618898+00:00
-- url     : https://prove2.me/submissions/1ece5476-5baa-4735-8b88-4093253bd1a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} (a0 : ℂ) (r : ℝ) (x : Xp p m) :
    Lsq (tailPt (sclPt a0 r x)) 1 = 1 + ‖a0‖ ^ 2 := by
  simp [Lsq, tailPt, sclPt]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
