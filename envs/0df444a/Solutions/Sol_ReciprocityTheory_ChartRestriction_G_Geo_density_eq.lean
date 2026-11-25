-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.density_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:08.65362+00:00
-- url     : https://prove2.me/submissions/32511e24-cb74-4db7-9fbf-35259a76cc16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pot_contDiffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_add_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eq_bsmul_of_segre_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_logNorm_bsmul


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
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {A : HermLine ι}
    {s : MRing ι} {P : Ideal (MRing ι)} (hs : IsSectionOn P A s)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
      logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y := by
  obtain ⟨a, ha, hsm, -⟩ := hs
  have hy0 := hy
  choose i0 hi0 using hy0
  obtain ⟨c, hc⟩ : ∃ c : (Fin e → ℂ) → K → ℂ,
      ∀ y' k, c y' k = γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := ⟨_, fun _ _ => rfl⟩
  have hnz : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 y, (∀ k, γ y' ⟨k, i0 k⟩ ≠ 0) ∧ (∀ k, c y' k ≠ 0) ∧
      γ' y' = bsmul (c y') (γ y') := by
    filter_upwards [hnz, hseg] with y' h0 hs'
    obtain ⟨h1, h2⟩ := eq_bsmul_of_segre_eq i0 h0 hs'
    have hcy : c y' = fun k => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := funext (hc y')
    refine ⟨h0, fun k => ?_, by rw [hcy]; exact h2⟩
    rw [hc]
    exact div_ne_zero (h1 k) (h0 k)
  obtain ⟨-, hc0, hyrel⟩ := hrel.self_of_nhds
  have hlog : logNorm A s (γ' y) = logNorm A s (γ y) := by
    rw [hyrel]
    exact logNorm_bsmul A ha hsm hc0 _
  rw [hlog]
  congr 1
  have hj : ∀ j, cxHessian (fun y' => pot L j (γ' y')) y = cxHessian (fun y' => pot L j (γ y')) y := by
    intro j
    have hcan : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := by
      intro k
      have hfun : (fun y' => c y' k) = fun y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ :=
        funext fun y' => hc y' k
      rw [hfun]
      exact (analyticAt_coord hγ' _).div (analyticAt_coord hγ _) (hi0 k)
    have hG : AnalyticAt ℂ
        (fun y' => ∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
      have hk : ∀ k, AnalyticAt ℂ
          (fun y' => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
        intro k
        refine analyticAt_const.mul (((hcan k).div analyticAt_const (hc0 k)).clog ?_)
        show c y k / c y k ∈ Complex.slitPlane
        rw [div_self (hc0 k)]
        exact Complex.one_mem_slitPlane
      have h := Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun (k : K) (y' : Fin e → ℂ) => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k))
        (c := y) Finset.univ (fun k _ => hk k)
      convert h using 1
      funext y'
      rw [Finset.sum_apply]
    have hev : (fun y' => pot L j (γ' y')) =ᶠ[𝓝 y] fun y' => pot L j (γ y') +
        (∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)).re +
        ∑ k, ((L j).a k : ℝ) * Real.log ‖c y k‖ := by
      filter_upwards [hrel] with y' hy'
      obtain ⟨h0, hck, h2⟩ := hy'
      have hpos : 0 < (L j).h (γ y') := (L j).pos _ fun k => ⟨i0 k, h0 k⟩
      have hne : ∀ k ∈ Finset.univ, ‖c y' k‖ ^ (L j).a k ≠ 0 :=
        fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hck k))
      have key : ∀ k, Real.log (‖c y' k‖ / ‖c y k‖) = Real.log ‖c y' k‖ - Real.log ‖c y k‖ :=
        fun k => Real.log_div (norm_ne_zero_iff.mpr (hck k)) (norm_ne_zero_iff.mpr (hc0 k))
      have hb : (L j).h (bsmul (c y') (γ y')) = (∏ k, ‖c y' k‖ ^ (L j).a k) * (L j).h (γ y') :=
        (L j).smul _ _ hck
      simp only [pot]
      rw [h2, hb, Real.log_mul (Finset.prod_ne_zero_iff.mpr hne) hpos.ne',
        Real.log_prod hne]
      simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re, norm_div, key,
        Real.log_zpow, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [cxHessian_congr hev]
    exact cxHessian_add_re _ (pot_contDiffAt (hL j) hγ hy) hG
  simp only [maDensity, hj]
end ReciprocityTheory.ChartRestriction.G.Geo
