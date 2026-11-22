-- Prove2me | solution 1 for SobolevL2.lca_sobolev_embedding
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:56:23.818442+00:00
-- url     : https://prove2.me/submissions/30c03e02-4923-4e2d-bfc0-231fdb9e091e

import Mathlib
import Theorems.Thm_LCAGroup_fourier_L1_to_zeroAtInfty_injective
import Theorems.Thm_LCAGroup_pontryagin_duality

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_SobolevL2_lca_sobolev_embedding

/-- Cauchy–Schwarz: for a positive measurable weight `a`, the `L¹(ν)` norm of `u` is bounded by
its `L²(a^{s/2} ν)` norm times `(∫ a^{-s/2} dν)^{1/2}`. -/
theorem lintegral_enorm_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha1 : ∀ x, 0 < a x) (s : ℝ) (u : X → ℂ)
    (hu : AEStronglyMeasurable u ν) :
    ∫⁻ χ, ‖u χ‖ₑ ∂ν ≤
      eLpNorm u 2 (ν.withDensity fun χ => ENNReal.ofReal (a χ ^ (s / 2))) *
        (∫⁻ χ, ENNReal.ofReal (a χ ^ (-s / 2)) ∂ν) ^ (1 / 2 : ℝ) := by
  set r : X → ℝ≥0∞ := fun χ => ENNReal.ofReal (a χ ^ (s / 4)) with hr
  set g : X → ℝ≥0∞ := fun χ => ENNReal.ofReal (a χ ^ (-s / 4)) with hg
  have hrg : ∀ χ, r χ * g χ = 1 := by
    intro χ
    simp only [hr, hg]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ha1 χ).le _), ← Real.rpow_add (ha1 χ)]
    have : s / 4 + -s / 4 = 0 := by ring
    rw [this, Real.rpow_zero, ENNReal.ofReal_one]
  have hr2 : ∀ χ, r χ ^ (2 : ℝ) = ENNReal.ofReal (a χ ^ (s / 2)) := by
    intro χ
    simp only [hr]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (ha1 χ).le _) (by norm_num),
      ← Real.rpow_mul (ha1 χ).le]
    congr 2
    ring
  have hg2 : ∀ χ, g χ ^ (2 : ℝ) = ENNReal.ofReal (a χ ^ (-s / 2)) := by
    intro χ
    simp only [hg]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (ha1 χ).le _) (by norm_num),
      ← Real.rpow_mul (ha1 χ).le]
    congr 2
    ring
  have hr_meas : Measurable r := (ha.pow_const (s / 4)).ennreal_ofReal
  have hg_meas : Measurable g := (ha.pow_const (-s / 4)).ennreal_ofReal
  have hρ_meas : Measurable fun χ => ENNReal.ofReal (a χ ^ (s / 2)) :=
    (ha.pow_const (s / 2)).ennreal_ofReal
  have h1 : ∫⁻ χ, ‖u χ‖ₑ ∂ν = ∫⁻ χ, ((fun χ => ‖u χ‖ₑ * r χ) * g) χ ∂ν := by
    refine lintegral_congr fun χ => ?_
    simp only [Pi.mul_apply, mul_assoc, hrg, mul_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (hu.enorm.mul hr_meas.aemeasurable) hg_meas.aemeasurable
  have h2 : ∫⁻ χ, (‖u χ‖ₑ * r χ) ^ (2 : ℝ) ∂ν =
      ∫⁻ χ, ‖u χ‖ₑ ^ (2 : ℝ) ∂(ν.withDensity fun χ => ENNReal.ofReal (a χ ^ (s / 2))) := by
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable ν hρ_meas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr fun χ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hr2, Pi.mul_apply, mul_comm]
  have h3 : eLpNorm u 2 (ν.withDensity fun χ => ENNReal.ofReal (a χ ^ (s / 2))) =
      (∫⁻ χ, ‖u χ‖ₑ ^ (2 : ℝ) ∂(ν.withDensity fun χ => ENNReal.ofReal (a χ ^ (s / 2)))) ^
        (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp
  rw [h1, h3, ← h2]
  refine hH.trans_eq ?_
  congr 2
  refine lintegral_congr fun χ => ?_
  exact hg2 χ

end Sol_SobolevL2_lca_sobolev_embedding


theorem solution {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (w : PontryaginDual G → ℝ≥0) (hw_cont : Continuous w)
    (hw_sub : ∃ C : ℝ≥0, 0 < C ∧ ∀ χ χ' : PontryaginDual G, w (χ * χ') ≤ C * (w χ + w χ'))
    (s : ℝ) (hs : 0 ≤ s)
    (hint : Integrable (fun χ => (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ u : PontryaginDual G → ℂ,
      MemLp u 2 (ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2))) →
      Integrable u ν ∧
      Continuous (fun x : G => ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν) ∧
      Tendsto (fun x : G => ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν) (cocompact G) (𝓝 0) ∧
      (∀ x : G, ‖∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν‖ₑ ≤
        C * eLpNorm u 2 (ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2)))) ∧
      ((∀ x : G, ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν = 0) → u =ᵐ[ν] 0) := by
  classical
  obtain ⟨F, hF, hFinj, -⟩ := LCAGroup.fourier_L1_to_zeroAtInfty_injective (PontryaginDual G) ν
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  have ha_cont : Continuous fun χ : PontryaginDual G => 1 + (w χ : ℝ) ^ 2 := by fun_prop
  have ha_meas : Measurable fun χ : PontryaginDual G => 1 + (w χ : ℝ) ^ 2 := ha_cont.measurable
  have ha_pos : ∀ χ : PontryaginDual G, 0 < 1 + (w χ : ℝ) ^ 2 := fun χ => by positivity
  set K : ℝ≥0∞ := (∫⁻ χ, ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ∂ν) ^ (1 / 2 : ℝ)
    with hK
  have hK_top : K ≠ ∞ := by
    rw [hK]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hint.lintegral_lt_top.ne
  refine ⟨K.toNNReal + 1, by positivity, ?_⟩
  intro u hu
  -- `ν` is absolutely continuous with respect to the weighted measure
  have hρ_meas : Measurable fun χ : PontryaginDual G =>
      ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2)) := (ha_meas.pow_const (s / 2)).ennreal_ofReal
  have hac : ν ≪ ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2)) :=
    withDensity_absolutelyContinuous' hρ_meas.aemeasurable
      (ae_of_all _ fun χ => (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (ha_pos χ) _)).ne')
  have hmeas : AEStronglyMeasurable u ν := hu.1.mono_ac hac
  have hbound : ∫⁻ χ, ‖u χ‖ₑ ∂ν ≤
      eLpNorm u 2 (ν.withDensity fun χ => ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2))) * K :=
    Sol_SobolevL2_lca_sobolev_embedding.lintegral_enorm_le ν
      (fun χ => 1 + (w χ : ℝ) ^ 2) ha_meas ha_pos s u hmeas
  have hint_u : Integrable u ν :=
    ⟨hmeas, lt_of_le_of_lt hbound (ENNReal.mul_lt_top hu.2 hK_top.lt_top)⟩
  set f : Lp ℂ 1 ν := hint_u.toL1 u with hf
  have hkey : ∀ x : G, ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν = F f (e x⁻¹) := by
    intro x
    rw [hF, RiemannMasullo.lcaFourier]
    refine integral_congr_ae ?_
    filter_upwards [hint_u.coeFn_toL1] with χ hχ
    rw [hχ, he, map_inv, Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj]
  have hΦ : (fun x : G => ∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν) = fun x => F f (e x⁻¹) :=
    funext hkey
  let h : G ≃ₜ PontryaginDual (PontryaginDual G) := (Homeomorph.inv G).trans e.toHomeomorph
  have hh : ∀ x, h x = e x⁻¹ := fun x => rfl
  refine ⟨hint_u, ?_, ?_, ?_, ?_⟩
  · rw [hΦ]
    have : (fun x : G => F f (e x⁻¹)) = (F f : PontryaginDual (PontryaginDual G) → ℂ) ∘ h := by
      funext x; rw [Function.comp_apply, hh]
    rw [this]
    exact (F f).continuous.comp h.continuous
  · rw [hΦ]
    have : (fun x : G => F f (e x⁻¹)) = (F f : PontryaginDual (PontryaginDual G) → ℂ) ∘ h := by
      funext x; rw [Function.comp_apply, hh]
    rw [this]
    exact ((F f).zero_at_infty').comp h.map_cocompact.le
  · intro x
    calc ‖∫ χ, u χ * ((χ x : Circle) : ℂ) ∂ν‖ₑ
        ≤ ∫⁻ χ, ‖u χ * ((χ x : Circle) : ℂ)‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ χ, ‖u χ‖ₑ ∂ν := by
          refine lintegral_congr fun χ => ?_
          rw [enorm_mul]
          have : ‖((χ x : Circle) : ℂ)‖ₑ = 1 := by
            rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
          rw [this, mul_one]
      _ ≤ eLpNorm u 2 (ν.withDensity fun χ =>
            ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2))) * K := hbound
      _ ≤ ((K.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) * eLpNorm u 2 (ν.withDensity fun χ =>
            ENNReal.ofReal ((1 + (w χ : ℝ) ^ 2) ^ (s / 2))) := by
          rw [mul_comm]
          gcongr
          rw [ENNReal.coe_add, ENNReal.coe_toNNReal hK_top]
          exact le_self_add
  · intro hzero
    have hFzero : F f = 0 := by
      ext ψ
      have := hkey (e.symm ψ)⁻¹
      rw [inv_inv, ContinuousMulEquiv.apply_symm_apply] at this
      rw [← this, hzero]
      rfl
    have hf0 : f = 0 := hFinj (by rw [hFzero, map_zero])
    have h1 : (f : PontryaginDual G → ℂ) =ᵐ[ν] u := hint_u.coeFn_toL1
    rw [hf0] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℂ 1 ν)
