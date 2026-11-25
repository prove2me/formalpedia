-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.kfa_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:41.146973+00:00
-- url     : https://prove2.me/submissions/1745fdd6-cea6-48b5-9be7-09e2fe5c8810

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_kfa_exp_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    Continuous (kfaKG ε hY) := by
  have hu : Continuous (kfaUnit Y) := by
    refine Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩
    show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))
    simpa only [smul_neg] using kfa_exp_cont (-Y)
  exact (hu.subtype_mk _).subtype_mk _
end ReciprocityTheory.ChartRestriction.DS.S7
