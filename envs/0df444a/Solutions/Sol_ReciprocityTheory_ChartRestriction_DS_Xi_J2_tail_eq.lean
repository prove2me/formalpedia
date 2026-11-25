-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:29.555135+00:00
-- url     : https://prove2.me/submissions/ca6a27f9-e22f-4fa8-a798-bd452a2ea4a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tailF_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tail_inner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons


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
theorem _root_.solution (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) :
    TailInt p m α ν = kc (2 + α + 2 * ∑ i, ν i) * CHInt p m (Function.update ν 0 (α + ν 0)) := by
  show ∫⁻ x : TDom p m, tailF p m α ν x = _
  rw [split_cons _ (tailF_meas p m α ν), lintegral_congr fun w => tail_inner p m α ν w,
    lintegral_mul_const _ (by fun_prop)]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
