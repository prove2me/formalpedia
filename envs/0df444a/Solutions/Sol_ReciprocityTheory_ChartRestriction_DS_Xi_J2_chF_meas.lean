-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.chF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:13.609445+00:00
-- url     : https://prove2.me/submissions/24a627f3-d324-4e32-bb21-9aeab610511c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_de


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
theorem _root_.solution (p m : ℕ) (ν : Fin (p + 1) → ℝ) : Measurable (chF p m ν) := by
  unfold chF
  exact Finset.measurable_prod _ fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
