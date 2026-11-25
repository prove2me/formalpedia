-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiff_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:50.853916+00:00
-- url     : https://prove2.me/submissions/9021c7fe-9e6e-462d-8ee2-50ede27a8c31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiff_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (i : ℕ) : ContDiff ℂ ω (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [dif_pos h]
    simp_rw [det_apply']
    refine ContDiff.sum fun σ _ => ?_
    refine contDiff_const.mul ?_
    exact contDiff_prod fun j _ => tb_contDiff_entry _ _
  · simp only [dif_neg h]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
