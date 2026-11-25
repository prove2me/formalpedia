-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.rhoSq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:17.074561+00:00
-- url     : https://prove2.me/submissions/10d89f55-35b2-457b-860a-2124024e0e19

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
theorem _root_.solution {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 0 = rhoSq x 1 + ‖x.2.1 0‖ ^ 2 := by
  simp only [rhoSq, Fin.sum_univ_succ]
  simp
  ring_nf
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
