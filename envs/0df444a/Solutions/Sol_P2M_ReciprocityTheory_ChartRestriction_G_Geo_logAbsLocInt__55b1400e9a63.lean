-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:59.577883+00:00
-- url     : https://prove2.me/submissions/a36669f1-90b7-46e8-bbfd-b1027be3f094

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_integrableOn_log_norm_closedBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology Real
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  by_cases h : ∃ z0 ∈ ball z (r / 5), f z0 ≠ 0
  · obtain ⟨z0, hz0, hfz0⟩ := h
    refine ⟨closedBall z0 (2 * (r / 5)), ?_,
      integrableOn_log_norm_closedBall hU hf (by positivity) ?_ hfz0⟩
    · apply mem_nhdsWithin_of_mem_nhds
      refine Filter.mem_of_superset (ball_mem_nhds z (by positivity : (0 : ℝ) < r / 5)) ?_
      intro x hx
      rw [mem_closedBall]
      rw [mem_ball] at hx hz0
      calc dist x z0 ≤ dist x z + dist z z0 := dist_triangle _ _ _
        _ ≤ 2 * (r / 5) := by rw [dist_comm z z0]; linarith
    · intro x hx
      apply hball
      rw [mem_ball] at hx hz0 ⊢
      calc dist x z ≤ dist x z0 + dist z0 z := dist_triangle _ _ _
        _ < r := by linarith
  · push_neg at h
    refine ⟨ball z (r / 5), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)), ?_⟩
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => by simp [h x hx]) measurableSet_ball
end ReciprocityTheory.ChartRestriction.G.Geo
