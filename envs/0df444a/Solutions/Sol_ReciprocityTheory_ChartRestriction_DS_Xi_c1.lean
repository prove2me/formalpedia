-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:52.925426+00:00
-- url     : https://prove2.me/submissions/0c578e10-84c0-43f6-b609-99d899916f72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailFinOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_bco_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_de_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lsq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lsq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_rhoSq_zero


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
theorem _root_.solution : C1 := by
  intro p m x
  rw [J2.de_sq, J2.de_sq, J2.lsq_zero, J2.rhoSq_zero, J2.bco_zero, J2.lsq_one]
  have hL : (0 : ℝ) < 1 + ((x.1 0).re * (x.1 0).re + (x.1 0).im * (x.1 0).im) := by
    nlinarith [mul_self_nonneg (x.1 0).re, mul_self_nonneg (x.1 0).im]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi
