-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.tailF_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:00.694254+00:00
-- url     : https://prove2.me/submissions/ef778f97-80a3-4a1f-8bb9-987be1dbdb38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_de
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_lsq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_tailPt


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
theorem _root_.solution (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) : Measurable (tailF p m α ν) := by
  unfold tailF
  have h := cont_tailPt (p := p) (m := m)
  exact ((ENNReal.measurable_ofReal.comp (((cont_lsq 1).comp h).measurable.pow_const _)).mul
    (ENNReal.measurable_ofReal.comp (((cont_de 1).comp h).measurable.pow_const _))).mul
    (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (((cont_de i.succ).comp h).measurable.pow_const _))
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
