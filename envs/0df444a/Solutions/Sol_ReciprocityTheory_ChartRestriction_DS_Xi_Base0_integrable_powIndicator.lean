-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_powIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:35.602907+00:00
-- url     : https://prove2.me/submissions/2aac247e-9826-44b3-a240-1715b45dec8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {β : ℝ} (hβ : β < 1) : Integrable (pw1 β) := by
  have hr : (-1 : ℝ) < -β := by linarith
  have h0 : IntervalIntegrable (fun t : ℝ => t ^ (-β)) volume 0 1 := by
    first
    | exact intervalIntegral.intervalIntegrable_rpow' hr
    | exact intervalIntegrable_rpow' hr
  have hpos : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h0 ⊢
    refine h0.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [abs_of_pos ht.1]
  have hneg : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using hpos.symm
  have hall : IntervalIntegrable (fun t : ℝ => |t| ^ (-β)) volume (-1) 1 := hneg.trans hpos
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at hall
  unfold pw1
  exact hall.integrable_indicator measurableSet_Icc
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
