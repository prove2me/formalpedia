-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.rankDrop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:14.546338+00:00
-- url     : https://prove2.me/submissions/6ac996e2-9d69-4e31-b223-5e3ce0f45f7e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_eventuallyEq
import Theorems.Thm_ReciprocityTheory_AnForm_M_potential_contDiffAt_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_pullback_local_eq
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_comp_eq_zero_of_rank_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : RankDropStatement := by
  intro e e' X Y _ _ A B h hh hrk Φ hΦ g
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_eq_zero fun j _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
    set x0 := h ((B.chart j).symm y) with hx0
    have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
    have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm)
        ((A.chart k ∘ h ∘ (B.chart j).symm) y) := fun i =>
      potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
        (by simp only [Function.comp_apply]; rw [hsymm]; exact (Φ i).mem_U x0)
    have h0 : locDens B (fun i => (Φ i).pullback h hh.1) j y = 0 := by
      unfold locDens
      refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
      exact maDens_comp_eq_zero_of_rank_lt _ _ y (hh.2 j k y ⟨hy, hk⟩) hφ (hrk j k y hy hk)
    rw [h0, mul_zero]
  · rfl
end ReciprocityTheory.AnForm.M
