-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_proof_e39964389368
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:08.245608+00:00
-- url     : https://prove2.me/submissions/a3b1f730-884a-461c-9e06-b11292bc31f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRankRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjMaxRankRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_det_ne_zero_of_chart_e4ac0590589f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
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
open GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
namespace GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
theorem _root_.solution : ProjMaxRankRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB y hy h0
  obtain ⟨i, hi, j, hj, hrank⟩ := hy
  have hsx : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hFd : DifferentiableAt ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)))
      (BV.chart j y) := (ProjRegular.proj_analyticAt Ψ hB y hj).differentiableAt
  have hF0 : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) 0 ≠ 0 := by
    rw [hsx]; exact h0
  have hFi : Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1)) i ≠ 0 := by
    rw [hsx]; exact hi

  have hkerA : LinearMap.ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ
      (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    rw [hrank, Module.finrank_fin_fun] at h
    exact Submodule.finrank_eq_zero.mp (by omega)

  have hG : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      fun u (l : Fin n) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0 := by
    filter_upwards [(ProjRegular.lift_analyticAt hB y hj).2] with u hu
    exact ProjRegular.projCoord_eq Ψ hu
  refine ⟨h0, fun k hk => ProjRegular.det_ne_zero_of_chart Ψ hB y h0 hk hj ?_⟩
  rw [hG.fderiv_eq]
  set F' := fderiv ℂ (fun u => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1))) (BV.chart j y)
  set Fu := Ψ (segre (R.lift y.1 ((BV.chart j).symm (BV.chart j y)).1))
  have hker : LinearMap.ker (fderiv ℂ (fun u (l : Fin n) =>
      Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) (Fin.succ l) /
        Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) 0) (BV.chart j y) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ l : Fin n, Fu 0 * F' v l.succ = Fu l.succ * F' v 0 := by
      intro l
      have h := congrFun hv l
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply] at h
      rw [fderiv_ratios_apply hFd Fin.succ 0 hF0] at h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · linear_combination h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hF0
    have hall : ∀ m : Fin (n + 1), Fu 0 * F' v m = Fu m * F' v 0 :=
      Fin.cases (by ring) hv'
    have hA : v ∈ LinearMap.ker (fderiv ℂ
        (fun u (l : Fin (n + 1)) => Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) l /
          Ψ (segre (R.lift y.1 ((BV.chart j).symm u).1)) i) (BV.chart j y) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) := by
      rw [LinearMap.mem_ker]
      funext m
      simp only [ContinuousLinearMap.coe_coe, Pi.zero_apply]
      rw [fderiv_ratios_apply hFd (fun l => l) i hFi]
      have h1 : Fu i * F' v m - Fu m * F' v i = 0 := by
        apply mul_left_cancel₀ hF0
        linear_combination Fu i * hall m - Fu m * hall i
      rw [h1, zero_div]
    rw [hkerA] at hA
    exact hA
  exact ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero
end GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular
