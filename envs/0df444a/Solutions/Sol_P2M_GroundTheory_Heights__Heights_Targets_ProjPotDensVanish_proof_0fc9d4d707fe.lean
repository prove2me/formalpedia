-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDensVanish_proof_0fc9d4d707fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:09:12.881097+00:00
-- url     : https://prove2.me/submissions/dfe76249-16ce-423f-a223-b4bd0515439c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDensVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankDropDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_analyticAt_4674083765d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_log_norm
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_comp_eq_zero_of_rank_lt
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjPotDensVanish
theorem _root_.solution : ProjPotDensVanish.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB hΨ j u hu hmax
  set x : V := (BV.chart j).symm u with hxdef
  have hx : x ∈ (BV.chart j).source := (BV.chart j).map_target hu
  have hxu : BV.chart j x = u := (BV.chart j).right_inv hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hΨ x.1 x.2)
  set G : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y => Ψ (segre (R.lift x.1 ((BV.chart j).symm y).1))
    with hG
  set τ : (Fin n → ℂ) → Fin (n + 1) → ℂ := fun y l => G y l / G y i with hτ
  have hGa : AnalyticAt ℂ G u := by
    have h := ProjRegular.proj_analyticAt Ψ hB x hx
    rwa [hxu] at h
  have hc : ∀ l, AnalyticAt ℂ (fun y => G y l) u := fun l => analyticAt_pi_iff.1 hGa l
  have hGi : G u i ≠ 0 := hi
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun l => (hc l).div (hc i) hGi
  have hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ u).toLinearMap) < n := by
    refine lt_of_le_of_ne ((LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun ℂ).le) ?_
    intro h
    apply hmax
    refine ⟨i, hi, j, hx, ?_⟩
    rw [hxu]
    exact h

  let φ' : (Fin (n + 1) → ℂ) → ℝ := fun w => Real.log (∑ l, ‖w l‖ ^ 2)
  have hsum_pos : ∀ w : Fin (n + 1) → ℂ, w i = 1 → 0 < ∑ l, ‖w l‖ ^ 2 := fun w hw =>
    lt_of_lt_of_le (by rw [hw]; norm_num)
      (Finset.single_le_sum (f := fun l => ‖w l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i))
  have hτ1 : ∀ y, G y i ≠ 0 → τ y i = 1 := fun y hy => div_self hy
  have hφ' : ContDiffAt ℝ 2 φ' (τ u) :=
    ((ContDiff.sum fun l _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ l)).contDiffAt.log
      (hsum_pos _ (hτ1 u hGi)).ne')

  let g : (Fin n → ℂ) → ℂ := fun y => G y i ^ 2
  have hga : AnalyticAt ℂ g u := (hc i).pow 2
  have hg0 : g u ≠ 0 := pow_ne_zero 2 hGi
  have hev : ∀ᶠ y in 𝓝 u, G y i ≠ 0 := (hc i).continuousAt.eventually_ne hGi
  have hgerm : (fun y' => (projPot R Ψ V).φ ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' ∘ τ) y + Real.log ‖g y‖ := by
    filter_upwards [hev] with y hy
    show Real.log (∑ l, ‖G y l‖ ^ 2) = Real.log (∑ l, ‖τ y l‖ ^ 2) + Real.log ‖G y i ^ 2‖
    have hn : ‖G y i‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have hs : ∑ l, ‖G y l‖ ^ 2 = ‖G y i‖ ^ 2 * ∑ l, ‖τ y l‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [τ, norm_div, div_pow]
      field_simp
    rw [hs, norm_pow, Real.log_mul (pow_ne_zero 2 hn) (hsum_pos _ (hτ1 y hy)).ne', add_comm]
  unfold locDens
  refine (maDens_congr_hessC _ (fun _ => φ' ∘ τ) u fun _ => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt (fun _ => φ') τ u hτa (fun _ => hφ') hrk)
  refine (hessC_congr_of_eventuallyEq hgerm).trans ?_
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g u
    (hφ'.comp u (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0
end ProjPotDensVanish
end GroundTheory.Heights₂.Heights.Targets
