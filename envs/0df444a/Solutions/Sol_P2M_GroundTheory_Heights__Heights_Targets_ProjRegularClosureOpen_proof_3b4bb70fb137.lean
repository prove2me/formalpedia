-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_proof_3b4bb70fb137
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:33.302366+00:00
-- url     : https://prove2.me/submissions/038f62b7-0670-4710-8c3d-58b815168574

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_analyticAt_projDet_8897a25a820a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_proj_analyticAt_of_mem_ce35ab46931c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open ProjRegularClosureOpen
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRegularClosureOpen
theorem _root_.solution : ProjRegularClosureOpen.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨j, hj⟩ := BV.cover x
  let S : Set (Fin n → ℂ) :=
    (BV.chart j).target ∩ (BV.chart j).symm ⁻¹' (Subtype.val ⁻¹' R.U x.1)
  have hSo : IsOpen S := (BV.chart j).isOpen_inter_preimage_symm
    ((R.isOpen_U x.1).preimage continuous_subtype_val)
  have hxS : BV.chart j x ∈ S :=
    ⟨(BV.chart j).map_source hj, by simp [(BV.chart j).left_inv hj, R.mem_U]⟩
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hSo _ hxS
  let F : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun v => Ψ (segre (R.lift x.1 ((BV.chart j).symm v).1))
  let h : (Fin n → ℂ) → ℂ := fun v => F v 0 * (projNumMat F v).det
  have hFa : ∀ u ∈ S, AnalyticAt ℂ F u := fun u hu => proj_analyticAt_of_mem Ψ hB x.1 hu.1 hu.2
  have hha : AnalyticOnNhd ℂ h (Metric.ball (BV.chart j x) r) := fun u hu =>
    analyticAt_projDet (hFa u (hrS hu))
  have hreg : ∀ u ∈ S, (BV.chart j).symm u ∈ projRegular R Ψ BV ↔ h u ≠ 0 := by
    intro u hu
    have hy : (BV.chart j).symm u ∈ (BV.chart j).source := (BV.chart j).map_target hu.1
    have hyu : BV.chart j ((BV.chart j).symm u) = u := (BV.chart j).right_inv hu.1
    have h0iff := ProjRegular.proj_ne_zero_iff Ψ (R := R) (hu.2 : ((BV.chart j).symm u).1 ∈ R.U x.1)
    have hev : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 u]
        fun v (i : Fin n) => F v i.succ / F v 0 := by
      filter_upwards [hSo.mem_nhds hu] with v hv
      exact ProjRegular.projCoord_eq Ψ hv.2
    constructor
    · rintro ⟨h0, hd⟩
      have hF0 : F u 0 ≠ 0 := h0iff.1 h0
      have hdj := hd j hy
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0] at hdj
      exact mul_ne_zero hF0 (right_ne_zero_of_mul hdj)
    · intro hh
      have hF0 : F u 0 ≠ 0 := left_ne_zero_of_mul hh
      have h0 := h0iff.2 hF0
      refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB _ h0 hk hy ?_⟩
      rw [hyu, hev.fderiv_eq, det_fderiv_div (hFa u hu) hF0]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hF0)))
        (right_ne_zero_of_mul hh)
  have hW : (BV.chart j).source ∩ (BV.chart j) ⁻¹' Metric.ball (BV.chart j x) r ∈ 𝓝 x :=
    ((BV.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hj, Metric.mem_ball_self hr⟩
  filter_upwards [hW] with y hyW
  obtain ⟨hys, hyb⟩ := hyW
  rw [mem_closure_iff_nhds]
  intro W hWy
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hz : h =ᶠ[𝓝 (BV.chart j y)] 0 := by
    have hc : ContinuousAt (BV.chart j).symm (BV.chart j y) :=
      (BV.chart j).continuousAt_symm ((BV.chart j).map_source hys)
    have hW' : W ∈ 𝓝 ((BV.chart j).symm (BV.chart j y)) := by
      rw [(BV.chart j).left_inv hys]; exact hWy
    filter_upwards [hc.preimage_mem_nhds hW', Metric.isOpen_ball.mem_nhds hyb] with v hvW hvB
    by_contra hv
    exact (Set.eq_empty_iff_forall_notMem.1 hne) _ ⟨hvW, (hreg v (hrS hvB)).2 hv⟩
  have hall := hha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hyb hz
  obtain ⟨z, hzW, hzreg⟩ := mem_closure_iff_nhds.1 hx _ hW
  exact ((hreg _ (hrS hzW.2)).1 (by rwa [(BV.chart j).left_inv hzW.1])) (hall hzW.2)
end ProjRegularClosureOpen
end GroundTheory.Heights₂.Heights.Targets
