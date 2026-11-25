-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:16.519384+00:00
-- url     : https://prove2.me/submissions/d0bd1dca-8647-4ecd-a977-c99dba4d706e

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_mul
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_inv
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_nm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_ae_unit
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_scale
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_kernel
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_FT
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_mul
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_scale
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_mul
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_ne_zero
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_measurable_reduced_size
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_rationalWeight_one
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_gauss
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_poly_le
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_of_le
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_pg
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_gm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_FT_gm
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) : ∃ Z : ℂ, ∀ H : (ι → ℂ) → ℂ, Integrable H →
    Integrable (fun x => H x * r0 κ e x) → Integrable (fun t => FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹)) →
    ∫ t, FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) = Z * ∫ x, H x * r0 κ e x := by
  let j₁ : (ι → ℂ) → ℂ := fun y => gm κ y * r0 κ e y
  let j₂ : (ι → ℂ) → ℂ := fun y => FT (gm κ) y⁻¹ * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹
  have e₁ : j₁ = fun y => ∏ w, ((‖y w‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖y w‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp only [j₁, gm, r0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hk : κ w ≠ 0 := by have := hκ w; omega
    by_cases hy : y w = 0
    · simp [hy, hk]
    · have hn : (‖y w‖ : ℂ) ≠ 0 := by simpa using hy
      have : conj (y w) * (y w / ‖y w‖) = ‖y w‖ := by
        rw [← mul_div_assoc, Complex.conj_mul', div_eq_iff hn]; ring
      push_cast
      calc _ = (conj (y w) * (y w / ‖y w‖)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e) * Complex.exp (-2 * Real.pi * (‖y w‖ : ℂ) ^ 2) := by
            rw [mul_pow]; ring
        _ = _ := by rw [this, pow_add]
  have i1 : ∀ s : ℕ, Integrable fun z : ℂ => ((‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) := fun s =>
    int_pg (by fun_prop) s fun z => by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hj₁ : Integrable j₁ := by
    rw [e₁]; exact Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => i1 _
  have hZ₁ : ∫ y, j₁ y ≠ 0 := by
    rw [e₁, integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ((‖z‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ))]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    refine (integral_pos_of_integrable_nonneg_nonzero (x := (1 : ℂ)) (by fun_prop) ?_ (fun z => by positivity) (by simp)).ne'
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using (i1 (κ w + 2 * e)).re
  have mg : Measurable (gm κ) := by unfold gm; fun_prop
  have mF : Measurable (FT (gm κ)) := (continuous_FT (integrable_gm κ)).measurable
  have mn : Measurable fun y : ι → ℂ => ((nm y : ℝ) : ℂ)⁻¹ := (Complex.continuous_ofReal.comp continuous_nm).measurable.inv
  have hj₂ : Integrable j₂ := by
    have e₂ : j₂ = fun y => ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * ((y w)⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖(y w)⁻¹‖ : ℂ) ^ 2)) *
        ((y w / (‖y w‖ : ℂ)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e)) * ((‖y w‖ : ℂ) ^ 2)⁻¹ := by
      funext y
      simp only [j₂, FT_gm, r0, nm, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Pi.inv_apply]
      push_cast; rfl
    rw [e₂]
    refine Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) (f := fun w z => (2⁻¹ * (-Complex.I) ^ κ w) *
      (z⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖z⁻¹‖ : ℂ) ^ 2)) * ((z / (‖z‖ : ℂ)) ^ κ w * (‖z‖ : ℂ) ^ (2 * e)) * ((‖z‖ : ℂ) ^ 2)⁻¹) fun w => ?_
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt (hκ w)
    refine int_of_le (by fun_prop) (Real.exp ((s + 3 : ℕ) ^ 2)) fun z hz => le_trans ?_ (poly_le ‖z‖⁻¹ (by positivity) (s + 3))
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hg := norm_gauss z⁻¹
    rw [norm_mul, norm_mul, norm_mul, norm_mul (z⁻¹ ^ κ w), hg]
    simp only [norm_mul, norm_pow, norm_inv, norm_neg, Complex.norm_I, one_pow, norm_div, Complex.norm_real, norm_norm,
      div_self hn.ne', mul_one, one_mul, Complex.norm_ofNat]
    have h2 : ‖z‖⁻¹ ^ s ≤ (1 + ‖z‖⁻¹) ^ s := pow_le_pow_left₀ (by positivity) (by linarith) s
    calc _ = 2⁻¹ * (‖z‖⁻¹ ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by
          rw [hs, pow_succ, pow_add, inv_pow _ (2 * e)]
          generalize ‖z‖⁻¹ ^ s = a
          have : ‖z‖ ^ (2 * e) ≠ 0 := by positivity
          generalize ‖z‖ ^ (2 * e) = b at *
          generalize Real.exp _ = c
          field_simp; ring
      _ ≤ 1 * ((1 + ‖z‖⁻¹) ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by gcongr; norm_num
      _ = _ := by ring
  refine ⟨(∫ y, j₂ y) / ∫ y, j₁ y, fun H hH hr hA => ?_⟩
  have k₁ := kernel (a := fun t => FT H t * (r0 κ e t)⁻¹) ((continuous_FT hH).measurable.mul (measurable_reduced_size κ e).inv).aestronglyMeasurable
    hj₁ (mg.mul (measurable_reduced_size κ e)) measurable_id (fun x hx => hx) (by simpa [mul_assoc] using hA)
  have hx' : ∀ᵐ x : ι → ℂ, H x * r0 κ e x = H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * ((nm x⁻¹ : ℝ) : ℂ)⁻¹ := by
    filter_upwards [ae_unit] with x hx
    have : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
    rw [nm_inv]; push_cast; field_simp
  have k₂ := kernel (a := fun x => H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹)) (hH.1.mul ((measurable_reduced_size κ e).mul mn).aestronglyMeasurable)
    hj₂ (((mF.comp measurable_inv).mul (measurable_reduced_size κ e)).mul mn) measurable_inv (fun x hx w => inv_ne_zero (hx w)) (hr.congr hx')
  rw [← integral_congr_ae hx', integral_integral_swap k₂.1] at k₂
  rw [integral_integral_swap k₁.1] at k₁
  have key : ∫ y, ∫ t, FT H t * (r0 κ e t)⁻¹ * j₁ (id t * y) = ∫ y, ∫ x, H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * j₂ (x⁻¹ * y) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with y hy
    have hny : ((nm y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hy).ne'
    calc _ = ∫ t, r0 κ e y * (FT H t * gm κ (y * t)) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with t ht
          have := rationalWeight_ne_zero κ e ht
          simp only [j₁, id, rationalWeight_mul, mul_comm t y]; field_simp
      _ = r0 κ e y * ∫ x, H x * FT (fun t => gm κ (y * t)) x := by
          rw [integral_const_mul, FT_mul hH (integrable_scale hy (integrable_gm κ))]
      _ = _ := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with x hx
          have hnx : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
          have h1 : r0 κ e x * r0 κ e x⁻¹ = 1 := by
            rw [← rationalWeight_mul, ← rationalWeight_one κ e]; congr 1; funext w; simp [hx w]
          have h2 : (x⁻¹ * y)⁻¹ = x * y⁻¹ := by funext w; simp [mul_comm]
          simp only [j₂, FT_scale (integrable_gm κ) hy, h2, rationalWeight_mul, nm_mul, nm_inv]
          push_cast
          generalize FT (gm κ) (x * y⁻¹) = A
          have h3 : ((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hnx
          rw [mul_inv, inv_inv]
          linear_combination (-(H x * A * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹)) * (((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) * h1 + h3)
  rw [k₁.2, k₂.2] at key
  simp only [id, mul_assoc] at key
  rw [div_mul_eq_mul_div, eq_div_iff hZ₁, key, mul_comm]
end PositivityTheory.ThKG.Loc.Bump
