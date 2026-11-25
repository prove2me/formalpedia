-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRankDropDens_proof_6cb0fdf04271
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:53.60094+00:00
-- url     : https://prove2.me/submissions/29af7489-686e-4520-bf71-ab155bc11e28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankDropDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankDropDens
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_log_norm
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoMap_preimage_mem_nhds
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_maDens_comp_eq_zero_of_rank_lt


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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.Targets
namespace ProjRankDropDens
theorem _root_.solution : ProjRankDropDens.Statement := by
  intro K _ ι _ P J n R L V BV hL hV j u hu p hp hrk
  set x : V := (BV.chart j).symm u with hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y => R.lift x.1 ((BV.chart j).symm y).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y q => G y q / G y ⟨q.1, p q.1⟩ with hτ
  obtain ⟨k₀, hk₀⟩ := R.A.cover x.1
  have hGa : ∀ q, AnalyticAt ℂ (fun y => G y q) u := by
    intro q
    have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y q) ∘ (R.A.chart k₀).symm) (R.A.chart k₀ x.1) :=
      R.holo x.1 q k₀ _ ⟨(R.A.chart k₀).map_source hk₀, by
        simp only [Set.mem_preimage, (R.A.chart k₀).left_inv hk₀]; exact R.mem_U _⟩
    have h2 : AnalyticAt ℂ (R.A.chart k₀ ∘ Subtype.val ∘ (BV.chart j).symm) u :=
      hV.2 j k₀ u ⟨hu, hk₀⟩
    refine (h1.comp_of_eq h2 rfl).congr ?_
    filter_upwards [holoMap_preimage_mem_nhds hV j k₀ hu hk₀] with y hy
    simp only [Function.comp_apply, G, (R.A.chart k₀).left_inv hy.2]
  have hc : ∀ᶠ y in 𝓝 u, ∀ k, G y ⟨k, p k⟩ ≠ 0 :=
    eventually_all.2 fun k => (hGa ⟨k, p k⟩).continuousAt.eventually_ne (hp k)
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun q => (hGa q).div (hGa ⟨q.1, p q.1⟩) (hp q.1)
  have hτ1 : ∀ y, (∀ k, G y ⟨k, p k⟩ ≠ 0) → ∀ k, τ y ⟨k, p k⟩ = 1 := fun y hy k => div_self (hy k)

  let E : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Nat.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Finite.equivFin (Σ k, ι k)).symm).toContinuousLinearEquiv
  let φ' : Fin n → (Fin (Nat.card (Σ k, ι k)) → ℂ) → ℝ := fun i z => Real.log ((L i).h (E.symm z))
  let τ' : (Fin n → ℂ) → (Fin (Nat.card (Σ k, ι k)) → ℂ) := ⇑E ∘ τ
  have hτ'a : AnalyticAt ℂ τ' u := (E.toContinuousLinearMap.analyticAt _).comp hτa
  have hφ' : ∀ i, ContDiffAt ℝ 2 (φ' i) (τ' u) := by
    intro i
    have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ u) :=
      Filter.mem_of_superset (eventually_all.2 fun k =>
        (continuous_apply (⟨k, p k⟩ : Σ k, ι k)).continuousAt.eventually_ne
          (show τ u ⟨k, p k⟩ ≠ 0 by rw [hτ1 u hp k]; exact one_ne_zero))
        fun z hz k => ⟨p k, hz k⟩
    have hlog : ContDiffAt ℝ ∞ (fun z => Real.log ((L i).h z)) (E.symm (τ' u)) := by
      simp only [τ', Function.comp_apply, E.symm_apply_apply]
      exact ((hL i).contDiffAt hS).log ((L i).pos _ fun k => ⟨p k, by rw [hτ1 u hp k]; exact one_ne_zero⟩).ne'
    exact (hlog.comp _ ((E.symm.contDiff (n := ∞)).restrict_scalars ℝ).contDiffAt).of_le
      (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

  let g : Fin n → (Fin n → ℂ) → ℂ := fun i y => ∏ k, G y ⟨k, p k⟩ ^ (L i).a k
  have hga : ∀ i, AnalyticAt ℂ (g i) u := fun i =>
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).zpow (hp k)
  have hg0 : ∀ i, g i u ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k)
  have hgerm : ∀ i, (fun y' => ((potOf R (L i)).pullback Subtype.val continuous_subtype_val).φ
      ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' i ∘ τ') y + Real.log ‖g i y‖ := by
    intro i
    filter_upwards [hc] with y hy
    show Real.log ((L i).h (G y)) = _
    have hGy : G y = fun q => G y ⟨q.1, p q.1⟩ * τ y q := by
      funext q
      simp only [τ]
      field_simp [hy q.1]
    have hs : (L i).h (G y) = (∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k) * (L i).h (τ y) := by
      conv_lhs => rw [hGy]
      exact (L i).smul (fun k => G y ⟨k, p k⟩) (τ y) hy
    have hpos : 0 < (L i).h (τ y) :=
      (L i).pos _ fun k => ⟨p k, by rw [hτ1 y hy k]; exact one_ne_zero⟩
    have hprod : 0 < ∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hy k)) _
    simp only [Function.comp_apply, φ', τ', E.symm_apply_apply, g, norm_prod, norm_zpow]
    rw [hs, Real.log_mul hprod.ne' hpos.ne', add_comm]
  have hrk' : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ' u).toLinearMap) < n := by
    have : LinearMap.range (fderiv ℂ τ' u).toLinearMap =
        (LinearMap.range (fderiv ℂ τ u).toLinearMap).map E.toLinearEquiv.toLinearMap := by
      rw [show τ' = ⇑E ∘ τ from rfl, E.comp_fderiv]
      exact LinearMap.range_comp (fderiv ℂ τ u).toLinearMap E.toLinearEquiv.toLinearMap
    rw [this, LinearEquiv.finrank_map_eq]
    exact hrk
  unfold locDens
  refine (maDens_congr_hessC _ (fun i => φ' i ∘ τ') u fun i => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt φ' τ' u hτ'a hφ' hrk')
  rw [hessC_congr_of_eventuallyEq (hgerm i)]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ (g i) u
    ((hφ' i).comp u (hτ'a.contDiffAt.restrict_scalars ℝ)) (hga i) (hg0 i)
end ProjRankDropDens
end GroundTheory.Heights₂.Heights.Targets
