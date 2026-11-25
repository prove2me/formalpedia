-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.sclL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:21.697056+00:00
-- url     : https://prove2.me/submissions/a085c481-6ab4-46c6-86db-8d38fcb8db2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) (t : ℝ) (x : Xp p m) :
    sclL p m t x = (t • x.1, t • x.2.1, t • x.2.2.1, t ^ 2 * x.2.2.2) := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
