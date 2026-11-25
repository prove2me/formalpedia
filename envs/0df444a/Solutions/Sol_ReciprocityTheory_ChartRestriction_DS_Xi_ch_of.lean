-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.ch_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:26.864699+00:00
-- url     : https://prove2.me/submissions/be2b57b7-2103-4e4e-b024-38b23a45b908

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_iic_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cond_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_ch_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_ch_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_kc_lt_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tail_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hC1 : C1) : CH := by
  intro p
  induction p with
  | zero =>
    intro m ν hν
    exact J2.ch_base m ν (by have := hν.1 0; rwa [J2.iic_zero] at this)
  | succ p ih =>
    intro m ν hν
    obtain ⟨h0, hs, hc⟩ := J2.cond_step ν hν
    rw [J2.ch_step, J2.tail_eq]
    exact ENNReal.mul_lt_top (J2.kc_lt_top (by linarith))
      (ENNReal.mul_lt_top (J2.kc_lt_top (by linarith)) (ih m _ hc))
end ReciprocityTheory.ChartRestriction.DS.Xi
