-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankMeetsPsi0_proof_2a27788e90e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:04.857191+00:00
-- url     : https://prove2.me/submissions/49c4eb81-0dac-44c3-8192-c3cc7caad762

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImportsAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_segre_lift_eq_2e320d5521fd
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
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
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjMaxRankMeetsPsi0
theorem _root_.solution : ProjMaxRankMeetsPsi0.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB y hy
  obtain ⟨i, hi, j, hj, hrank⟩ := hy
  by_cases h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0
  · exact ⟨y, mem_connectedComponent, ⟨i, hi, j, hj, hrank⟩, h0⟩
  rw [not_not] at h0
  have hi0 : i ≠ 0 := by rintro rfl; exact hi h0
  have hsx : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hu0 : BV.chart j y ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hc : ∀ l, AnalyticAt ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l)
      (BV.chart j y) := fun l => analyticAt_pi_iff.1 (ProjRegular.proj_analyticAt Ψ hB y hj) l
  have hiu : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) i ≠ 0 := by rwa [hsx]
  set A : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun u l =>
    Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i with hAdef
  have hA : AnalyticAt ℂ A (BV.chart j y) := analyticAt_pi_iff.2 fun l => (hc l).div (hc i) hiu
  have hDi : ∀ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i ≠ 0 :=
    (hc i).continuousAt.eventually_ne hiu

  have hrk : ∀ᶠ u in 𝓝 (BV.chart j y),
      (n : Cardinal) ≤ (fderiv ℂ A u : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)).rank := by
    refine hA.fderiv.continuousAt.preimage_mem_nhds
      ((isOpen_setOfPred_nat_le_rank (𝕜 := ℂ) n).mem_nhds ?_)
    show (n : Cardinal) ≤ _
    rw [LinearMap.rank, ← Module.finrank_eq_rank, hrank]

  have hfr : ∃ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 ≠ 0 := by
    intro hz
    have hz' : ∀ᶠ u in 𝓝 (BV.chart j y), Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 = 0 :=
      hz.mono fun u hu => not_not.1 hu
    have hD := hA.differentiableAt.hasFDerivAt
    have hD0 : (ContinuousLinearMap.proj 0).comp (fderiv ℂ A (BV.chart j y)) = 0 :=
      (hasFDerivAt_pi'.1 hD 0).unique ((hasFDerivAt_const (0 : ℂ) _).congr_of_eventuallyEq
        (by filter_upwards [hz'] with u hu; simp [hAdef, hu]))
    have hDi' : (ContinuousLinearMap.proj i).comp (fderiv ℂ A (BV.chart j y)) = 0 :=
      (hasFDerivAt_pi'.1 hD i).unique ((hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq
        (by filter_upwards [hDi] with u hu; simp [hAdef, div_self hu]))
    let π : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := LinearMap.pi fun t => LinearMap.proj (![0, i] t)
    have hπ : LinearMap.range π = ⊤ := by
      refine LinearMap.range_eq_top.2 fun w => ⟨Pi.single 0 (w 0) + Pi.single i (w 1), ?_⟩
      funext t
      fin_cases t <;> simp [π, hi0, Ne.symm hi0]
    have hker := LinearMap.finrank_range_add_finrank_ker π
    rw [hπ, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hker
    have hle : LinearMap.range (fderiv ℂ A (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) ≤
        LinearMap.ker π := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      funext t
      have e0 := DFunLike.congr_fun hD0 v
      have ei := DFunLike.congr_fun hDi' v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        zero_apply] at e0 ei
      fin_cases t <;> simp [π, e0, ei]
    have hmono := Submodule.finrank_mono hle
    rw [hrank] at hmono
    have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    have := i.isLt
    omega
  have hev : ∀ᶠ u in 𝓝 (BV.chart j y), u ∈ (BV.chart j).target ∧
      ((BV.chart j).symm u).1 ∈ R.U y.1 ∧
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i ≠ 0 ∧
      (n : Cardinal) ≤ (fderiv ℂ A u : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)).rank := by
    filter_upwards [(BV.chart j).open_target.mem_nhds hu0, (ProjRegular.lift_analyticAt hB y hj).2,
      hDi, hrk] with u h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨u, hu0', hub⟩ := (hfr.and_eventually (Metric.ball_mem_nhds _ hε)).exists
  obtain ⟨hut, huU, hui, hurk⟩ := hball u hub
  refine ⟨(BV.chart j).symm u, ?_, ⟨i, ?_, j, (BV.chart j).map_target hut, ?_⟩,
    (ProjRegular.proj_ne_zero_iff Ψ huU).2 hu0'⟩
  ·
    refine ((convex_ball _ _).isPreconnected.image _
      ((BV.chart j).continuousOn_symm.mono fun w hw => (hball w hw).1)).subset_connectedComponent
      ⟨_, Metric.mem_ball_self hε, hsx⟩ ⟨u, hub, rfl⟩
  · obtain ⟨c, hc0, hcq⟩ := ProjRegular.proj_segre_lift_eq Ψ huU
    rw [hcq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc0 hui
  ·
    have hU' : ∀ᶠ w in 𝓝 u, ((BV.chart j).symm w).1 ∈ R.U ((BV.chart j).symm u).1 :=
      (continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hut)).preimage_mem_nhds
        ((R.isOpen_U _).mem_nhds (R.mem_U _))
    have heq : (fun w l => Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) l /
        Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) i) =ᶠ[𝓝 u] A := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hub, hU'] with w hw hwU
      obtain ⟨c1, hc1, h1⟩ := ProjRegular.proj_segre_lift_eq Ψ (hball w hw).2.1
      obtain ⟨c2, hc2, h2⟩ := ProjRegular.proj_segre_lift_eq Ψ hwU
      have hb : Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm w).1)) =
          (c2⁻¹ * c1) • Ψ (segre (R.lift y.1 ((BV.chart j).symm w).1)) := by
        rw [mul_smul, ← h1, h2, smul_smul, inv_mul_cancel₀ hc2, one_smul]
      funext l
      simp only [hAdef, hb, Pi.smul_apply, smul_eq_mul]
      exact mul_div_mul_left _ _ (mul_ne_zero (inv_ne_zero hc2) hc1)
    rw [(BV.chart j).right_inv hut, heq.fderiv_eq]
    rw [LinearMap.rank, ← Module.finrank_eq_rank] at hurk
    exact le_antisymm ((LinearMap.finrank_range_le _).trans (by simp)) (by exact_mod_cast hurk)
end ProjMaxRankMeetsPsi0
end GroundTheory.Heights₂.Heights.Targets
