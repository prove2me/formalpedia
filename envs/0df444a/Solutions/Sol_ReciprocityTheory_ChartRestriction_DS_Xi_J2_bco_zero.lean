-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.bco_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:15.483272+00:00
-- url     : https://prove2.me/submissions/82908dd7-f3f0-4800-838c-0a5df78cae1e

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
theorem _root_.solution {p m : ℕ} (x : Xp (p + 1) m) : bco x 0 = bco x 1 - x.2.1 0 * star (x.1 0) := by
  simp only [bco, Fin.sum_univ_succ]
  simp
  ring_nf
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
