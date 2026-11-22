-- Prove2me | solution 1 for SobolevL2.sobolevNorm_neg_eq_dual_norm
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:47:50.604249+00:00
-- url     : https://prove2.me/submissions/f2f32612-b5c5-42c8-a893-d260055c0af6

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv

set_option autoImplicit false

open SobolevL2

namespace Sol_SobolevL2_sobolevNorm_neg_eq_dual_norm

variable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Transpose identity: `(J^s u)(φ) = u(J^s φ)` (the symbol is even). -/
theorem besselPotential_apply_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (s : ℝ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    besselPotential E F s u φ =
      u (SchwartzMap.fourierMultiplierCLM ℂ
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ) := by
  have hm : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [besselPotential, fourierMultiplierCLM_apply_apply]
  congr 1
  ext x
  rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourier_coe,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_comp_neg]
  refine congrArg (fun f : E → ℂ => 𝓕 f x) ?_
  funext y
  rw [SchwartzMap.smulLeftCLM_apply_apply hm, SchwartzMap.smulLeftCLM_apply_apply hm, norm_neg,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  rfl

/-- `J^s J^{-s} = id` on Schwartz functions. -/
theorem fourierMultiplier_neg_cancel (s : ℝ) (ψ : 𝓢(E, ℂ)) :
    SchwartzMap.fourierMultiplierCLM ℂ (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
      (SchwartzMap.fourierMultiplierCLM ℂ
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ) = ψ := by
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  have h1 : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) *
      (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ))) = fun _ ↦ (1 : ℂ) := by
    funext x
    rw [Pi.mul_apply, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    simp [neg_div]
  rw [h1, SchwartzMap.fourierMultiplierCLM_const]
  simp

/-- If `J^s u` is represented by `f ∈ L²`, then `‖u‖_{H^s} = ‖f‖ₑ`. -/
theorem sobolevNorm_eq_of_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (s : ℝ) (u : 𝓢'(E, F)) (f : Lp F 2 (volume : Measure E))
    (hf : besselPotential E F s u = f) : sobolevNorm s u = ‖f‖ₑ := by
  have hinj : ∀ g h : Lp F 2 (volume : Measure E), (g : 𝓢'(E, F)) = h → g = h := by
    intro g h hgh
    exact LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E)) (p := 2)) hgh
  unfold sobolevNorm
  apply le_antisymm
  · exact iInf₂_le (α := ℝ≥0∞) f hf
  · refine le_iInf₂ fun g hg => ?_
    rw [hinj g f (hg.symm.trans hf)]

/-- The `H^s` norm of a Schwartz function is the `L²` norm of `J^s φ`. -/
theorem sobolevNorm_schwartz (s : ℝ) (φ : 𝓢(E, ℂ)) :
    sobolevNorm s (φ : 𝓢'(E, ℂ)) =
      ‖(SchwartzMap.fourierMultiplierCLM ℂ
        (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ).toLp 2 (volume : Measure E)‖ₑ := by
  apply sobolevNorm_eq_of_eq
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

/-- Cauchy–Schwarz for the pairing of an `L²` function with a Schwartz function. -/
theorem enorm_pairing_le (g : Lp ℂ 2 (volume : Measure E)) (ψ : 𝓢(E, ℂ)) :
    ‖(g : 𝓢'(E, ℂ)) ψ‖ₑ ≤ ‖ψ.toLp 2 (volume : Measure E)‖ₑ * ‖g‖ₑ := by
  rw [Lp.toTemperedDistribution_apply]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := (volume : Measure E))
    (Lp.aestronglyMeasurable g) ψ.continuous.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  rw [Lp.enorm_def, Lp.enorm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp ψ 2 volume)]
  exact h

/-- `L²` duality on Schwartz functions (Hahn–Banach + Riesz): a tempered distribution bounded by
`C` on the unit ball of `𝓢` for the `L²` norm is an `L²` function of norm at most `C`. -/
theorem exists_Lp_of_bounded (w : 𝓢'(E, ℂ)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hw : ∀ ψ : 𝓢(E, ℂ), ‖ψ.toLp 2 (volume : Measure E)‖ₑ ≤ 1 → ‖w ψ‖ₑ ≤ C) :
    ∃ g : Lp ℂ 2 (volume : Measure E), (g : 𝓢'(E, ℂ)) = w ∧ ‖g‖ₑ ≤ C := by
  set c : ℝ := C.toReal with hc_def
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hinj : Function.Injective (fun f : 𝓢(E, ℂ) ↦ f.toLp 2 (volume : Measure E)) :=
    SchwartzMap.injective_toLp 2 volume
  -- the bound `‖w ψ‖ ≤ c ‖ψ‖_{L²}`
  have hbound : ∀ ψ : 𝓢(E, ℂ), ‖w ψ‖ ≤ c * ‖ψ.toLp 2 (volume : Measure E)‖ := by
    intro ψ
    by_cases h0 : ψ.toLp 2 (volume : Measure E) = 0
    · have hψ : ψ = 0 := by
        apply hinj
        simp only
        rw [h0]
        exact ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)).map_zero).symm
      rw [hψ, map_zero, norm_zero]
      exact mul_nonneg hc0 (norm_nonneg _)
    · set t : ℝ := ‖ψ.toLp 2 (volume : Measure E)‖ with ht_def
      have ht : 0 < t := norm_pos_iff.mpr h0
      have hsmul : (((t : ℂ)⁻¹) • ψ).toLp 2 (volume : Measure E) =
          ((t : ℂ)⁻¹) • ψ.toLp 2 (volume : Measure E) :=
        (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)).map_smul _ _
      have hnorm1 : ‖(((t : ℂ)⁻¹) • ψ).toLp 2 (volume : Measure E)‖ = 1 := by
        rw [hsmul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
          ← ht_def, inv_mul_cancel₀ ht.ne']
      have h1 : ‖w (((t : ℂ)⁻¹) • ψ)‖ₑ ≤ C := by
        apply hw
        rw [← ofReal_norm, hnorm1, ENNReal.ofReal_one]
      have h2 : ‖w (((t : ℂ)⁻¹) • ψ)‖ ≤ c := by
        rw [hc_def, ← toReal_enorm]
        exact ENNReal.toReal_mono hC h1
      rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h2
      rw [mul_comm]
      rwa [inv_mul_le_iff₀ ht] at h2
  -- the functional on the range of `𝓢 → L²`
  let T : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap
  have hT : Function.Injective T := hinj
  let e := LinearEquiv.ofInjective T hT
  let ℓ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    { toFun := fun x => w (e.symm x)
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by intro a x; simp only [map_smul, RingHom.id_apply] }
  have hℓ₀ : ∀ x : LinearMap.range T, ‖ℓ₀ x‖ ≤ c * ‖x‖ := by
    intro x
    have hx : (x : Lp ℂ 2 (volume : Measure E)) = (e.symm x).toLp 2 (volume : Measure E) := by
      conv_lhs => rw [← e.apply_symm_apply x]
      rfl
    change ‖w (e.symm x)‖ ≤ c * ‖x‖
    rw [← Submodule.norm_coe, hx]
    exact hbound _
  let ℓ : StrongDual ℂ (LinearMap.range T) := ℓ₀.mkContinuous c hℓ₀
  have hℓn : ‖ℓ‖ ≤ c := LinearMap.mkContinuous_norm_le ℓ₀ hc0 hℓ₀
  obtain ⟨Λ, hΛ, hΛn⟩ := exists_extension_norm_eq (LinearMap.range T) ℓ
  -- Riesz representation
  set h : Lp ℂ 2 (volume : Measure E) := (InnerProductSpace.toDual ℂ _).symm Λ with hh_def
  have hhn : ‖h‖ = ‖Λ‖ := LinearIsometryEquiv.norm_map _ _
  refine ⟨star h, ?_, ?_⟩
  · ext ψ
    rw [Lp.toTemperedDistribution_apply]
    have hΛψ : Λ (ψ.toLp 2 (volume : Measure E)) = w ψ := by
      have := hΛ (e ψ)
      have he : ((e ψ : LinearMap.range T) : Lp ℂ 2 (volume : Measure E)) =
          ψ.toLp 2 (volume : Measure E) := rfl
      rw [he] at this
      rw [this]
      change w (e.symm (e ψ)) = w ψ
      rw [e.symm_apply_apply]
    have hR : Λ (ψ.toLp 2 (volume : Measure E)) =
        inner ℂ h (ψ.toLp 2 (volume : Measure E)) := by
      rw [hh_def, InnerProductSpace.toDual_symm_apply]
    rw [← hΛψ, hR, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star h, ψ.coeFn_toLp 2 (volume : Measure E)] with x hx1 hx2
    rw [hx1, hx2, Pi.star_apply, smul_eq_mul, RCLike.inner_apply]
    rfl
  · have hn : ‖star h‖ = ‖h‖ := by
      rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star h), eLpNorm_star]
    rw [← ofReal_norm, hn, hhn, hΛn, ← ENNReal.ofReal_toReal hC]
    exact ENNReal.ofReal_le_ofReal hℓn

end Sol_SobolevL2_sobolevNorm_neg_eq_dual_norm

open Sol_SobolevL2_sobolevNorm_neg_eq_dual_norm in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (s : ℝ) (v : 𝓢'(E, ℂ)) :
    sobolevNorm (-s) v =
      ⨆ (φ : 𝓢(E, ℂ)) (_ : sobolevNorm s (φ : 𝓢'(E, ℂ)) ≤ 1), ‖v φ‖ₑ := by
  apply le_antisymm
  · -- `‖v‖_{H^{-s}} ≤ sup`: Riesz representation applied to `J^{-s} v`
    set C : ℝ≥0∞ := ⨆ (φ : 𝓢(E, ℂ)) (_ : sobolevNorm s (φ : 𝓢'(E, ℂ)) ≤ 1), ‖v φ‖ₑ
      with hC_def
    by_cases hCtop : C = ⊤
    · rw [hCtop]
      exact le_top
    · have hw : ∀ ψ : 𝓢(E, ℂ), ‖ψ.toLp 2 (volume : Measure E)‖ₑ ≤ 1 →
          ‖besselPotential E ℂ (-s) v ψ‖ₑ ≤ C := by
        intro ψ hψ
        rw [besselPotential_apply_eq]
        refine le_iSup₂_of_le (f := fun (φ : 𝓢(E, ℂ))
          (_ : sobolevNorm s (φ : 𝓢'(E, ℂ)) ≤ 1) => ‖v φ‖ₑ) _ ?_ le_rfl
        rw [sobolevNorm_schwartz, fourierMultiplier_neg_cancel]
        exact hψ
      obtain ⟨g, hg, hgC⟩ := exists_Lp_of_bounded _ C hCtop hw
      exact (sobolevNorm_eq_of_eq (-s) v g hg.symm).le.trans hgC
  · -- `sup ≤ ‖v‖_{H^{-s}}`: Cauchy–Schwarz
    refine le_iInf₂ (α := ℝ≥0∞) fun g hg => ?_
    refine iSup₂_le fun φ hφ => ?_
    have hv : v = besselPotential E ℂ s (g : 𝓢'(E, ℂ)) := by
      rw [← hg, besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero]
      rfl
    rw [hv, besselPotential_apply_eq]
    calc ‖(g : 𝓢'(E, ℂ)) (SchwartzMap.fourierMultiplierCLM ℂ
            (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ)‖ₑ
        ≤ ‖(SchwartzMap.fourierMultiplierCLM ℂ
            (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ).toLp 2 (volume : Measure E)‖ₑ *
            ‖g‖ₑ := enorm_pairing_le g _
      _ ≤ 1 * ‖g‖ₑ := by
          gcongr
          rw [← sobolevNorm_schwartz]
          exact hφ
      _ = ‖g‖ₑ := one_mul _
