-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_proof_fc9ef9b3bcd2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:59.859244+00:00
-- url     : https://prove2.me/submissions/c00a9f40-f18a-495e-8e74-5b9d28bba2f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_analyticAt_chart_4620b31d9b76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
import Theorems.Thm_ReciprocityTheory_AnForm_volume_eq_zero_of_locally_in_analytic_zero_set


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRegularNull
theorem _root_.solution : ProjRegularNull.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB _ _ j
  set T := (BV.chart j).target ∩ (BV.chart j).symm ⁻¹'
    (interior (closure (projRegular R Ψ BV)) \ projRegular R Ψ BV) with hT

  have hreg : ∀ z ∈ T, ∀ r > 0, ball z r ⊆ (BV.chart j).target →
      ∃ w ∈ ball z r, (BV.chart j).symm w ∈ projRegular R Ψ BV := by
    intro z hz r hr hWt
    obtain ⟨y, ⟨w, hw, rfl⟩, hyr⟩ := mem_closure_iff.1 (interior_subset hz.2.1) _
      ((BV.chart j).isOpen_image_symm_of_subset_target isOpen_ball hWt) ⟨z, mem_ball_self hr, rfl⟩
    exact ⟨w, hw, hyr⟩
  let Z : Set (Fin n → ℂ) := {u | Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1)) 0 = 0}
  have hA : volume (T ∩ Z) = 0 := by
    refine ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _ fun z hz => ?_
    set x0 := (BV.chart j).symm z
    have hx0 : x0 ∈ (BV.chart j).source := (BV.chart j).map_target hz.1.1
    have hz0 : BV.chart j x0 = z := (BV.chart j).right_inv hz.1.1
    have hF := analyticAt_pi_iff.1 (ProjRegular.proj_analyticAt Ψ hB x0 hx0) 0
    have hU := (ProjRegular.lift_analyticAt hB x0 hx0).2
    rw [hz0] at hF hU
    obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 (hF.eventually_analyticAt.and
      (hU.and ((BV.chart j).open_target.mem_nhds hz.1.1)))
    obtain ⟨w, hw, hwr⟩ := hreg z hz.1 r hr fun u hu => (hP u hu).2.2
    refine ⟨ball z r, isOpen_ball, mem_ball_self hr, (convex_ball z r).isPreconnected, _,
      fun u hu => (hP u hu).1, ⟨w, hw, ?_⟩, fun u hu => ?_⟩
    · exact (ProjRegular.proj_ne_zero_iff Ψ (hP w hw).2.1).1 hwr.1
    · by_contra h
      exact (ProjRegular.proj_ne_zero_iff Ψ (hP u hu.2).2.1).2 h hu.1.2
  have hB' : volume (T ∩ Zᶜ) = 0 := by
    refine ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set _ fun z hz => ?_
    set x0 := (BV.chart j).symm z
    have hx0 : x0 ∈ (BV.chart j).source := (BV.chart j).map_target hz.1.1
    have hz0 : BV.chart j x0 = z := (BV.chart j).right_inv hz.1.1
    have hq := ProjRegular.analyticAt_chart Ψ hB x0 hz.2 j hx0
    rw [hz0] at hq
    obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1 (hq.eventually_analyticAt.and
      ((BV.chart j).open_target.mem_nhds hz.1.1))
    obtain ⟨w, hw, hwr⟩ := hreg z hz.1 r hr fun u hu => (hP u hu).2
    refine ⟨ball z r, isOpen_ball, mem_ball_self hr, (convex_ball z r).isPreconnected, _,
      fun u hu => ProjRegularNull.analyticAt_det_fderiv (hP u hu).1, ⟨w, hw, ?_⟩, fun u hu => ?_⟩
    · have h := hwr.2 j ((BV.chart j).map_target (hP w hw).2)
      rwa [(BV.chart j).right_inv (hP w hw).2] at h
    · by_contra hd
      refine hu.1.1.2.2 ⟨hu.1.2, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB _ hu.1.2 hk
        ((BV.chart j).map_target hu.1.1.1) ?_⟩
      rwa [(BV.chart j).right_inv hu.1.1.1]
  refine measure_mono_null (fun u hu => ?_) (measure_union_null hA hB')
  by_cases h : u ∈ Z
  · exact Or.inl ⟨hu, h⟩
  · exact Or.inr ⟨hu, h⟩
end ProjRegularNull
end GroundTheory.Heights₂.Heights.Targets
