-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDensPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:04.3673+00:00
-- url     : https://prove2.me/submissions/48adcca4-3a16-4e84-aae6-4bfba2baa0ec

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_eventuallyEq
import Theorems.Thm_ReciprocityTheory_AnForm_M_potential_contDiffAt_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_pullback_local_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


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
theorem _root_.solution : LocDensPullbackStatement := by
  intro e X Y _ _ A B h hh Φ hΦ j k y hy hk
  set x0 := h ((B.chart j).symm y) with hx0
  set τ := A.chart k ∘ h ∘ (B.chart j).symm with hτ
  have hτa : AnalyticAt ℂ τ y := hh.2 j k y ⟨hy, hk⟩
  have hτy : τ y = A.chart k x0 := rfl
  have hsymm : (A.chart k).symm (A.chart k x0) = x0 := (A.chart k).left_inv hk
  have hφ : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ x0 ∘ (A.chart k).symm) (τ y) := by
    intro i
    rw [hτy]
    exact potential_contDiffAt_chart (hΦ i) x0 k ((A.chart k).map_source hk)
      (by rw [hsymm]; exact (Φ i).mem_U x0)
  unfold locDens
  refine (maDens_congr_eventuallyEq (fun i => pullback_local_eq hh (Φ i) j k hy hk)).trans ?_
  rw [hsymm]
  refine (ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ x0 ∘ (A.chart k).symm) τ y hτa hφ).trans ?_
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hτy]
  rfl
end ReciprocityTheory.AnForm.M
