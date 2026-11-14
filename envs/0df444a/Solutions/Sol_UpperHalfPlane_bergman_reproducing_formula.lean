-- Prove2me | solution 1 for UpperHalfPlane.bergman_reproducing_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T00:46:10.778249+00:00
-- url     : https://prove2.me/submissions/0de0573e-7822-4d4c-875e-a0d6981a1809

import Mathlib
import Definitions.Def_RPLib_S3_Bergman

set_option autoImplicit false

namespace UploadBergman

open MeasureTheory Complex UpperHalfPlane RamanujanPetersson.Bergman
open scoped ComplexConjugate Manifold

/-- The reproducing formula on `{z : ℂ | 0 < z.im}` with Lebesgue measure and density `(Im z)⁻²`,
from the library version on `ℍ` with Mathlib's hyperbolic measure. -/
theorem main (k : ℕ) (hk : 3 ≤ k) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (C : ℝ)
    (hC : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ C / z.im ^ ((k : ℝ) / 2)) (w : ℂ) (hw : 0 < w.im) :
    MeasureTheory.IntegrableOn
        (fun z : ℂ => f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k *
          ((z.im : ℂ) ^ 2)⁻¹)
        {z : ℂ | 0 < z.im} ∧
      ∫ z in {z : ℂ | 0 < z.im},
          f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k * ((z.im : ℂ) ^ 2)⁻¹ =
        4 * (Real.pi : ℂ) * Complex.I ^ k / (((k : ℂ) - 1) * 2 ^ k) * f w := by
  let g : ℍ → ℂ := fun z => f (z : ℂ)
  let W : ℍ := ⟨w, hw⟩
  have hgd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hf.congr (fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp only [g, Function.comp_apply, ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk]
  have hgC : ∀ z : ℍ, ‖g z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := fun z => hC (z : ℂ) z.im_pos
  let F : ℍ → ℂ := fun z => g z * conj ((((z : ℂ) - conj (W : ℂ)) ^ k)⁻¹) * ((z.im : ℂ)) ^ k
  have hS : MeasurableSet {z : ℂ | 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hpt : Set.EqOn (fun z : ℂ => ((z.im) ^ 2)⁻¹ • F (ofComplex z))
      (fun z : ℂ => f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k *
          ((z.im : ℂ) ^ 2)⁻¹) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    simp only [F, g, W, ofComplex_apply_of_im_pos hz']
    have him : (((⟨z, hz'⟩ : ℍ).im : ℝ) : ℂ) = (z.im : ℂ) := rfl
    rw [Complex.real_smul]
    push_cast
    rw [him]
    ring
  have hint : Integrable F := integrable_reproducing_of_bound hk hgd.continuous W hgC
  refine ⟨((integrable_iff_integrableOn F).mp hint).congr_fun hpt hS, ?_⟩
  have h1 : ∫ z : ℍ, F z = bergmanConst k * g W := bergman_reproducing_of_bound hk hgd W hgC
  rw [RamanujanPetersson.Bergman.integral_eq_setIntegral, setIntegral_congr_fun hS hpt] at h1
  rw [h1, bergmanConst]

end UploadBergman

theorem solution (k : ℕ) (hk : 3 ≤ k) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (C : ℝ)
    (hC : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ C / z.im ^ ((k : ℝ) / 2)) (w : ℂ) (hw : 0 < w.im) :
    MeasureTheory.IntegrableOn
        (fun z : ℂ => f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k *
          ((z.im : ℂ) ^ 2)⁻¹)
        {z : ℂ | 0 < z.im} ∧
      ∫ z in {z : ℂ | 0 < z.im},
          f z * starRingEnd ℂ (((z - starRingEnd ℂ w) ^ k)⁻¹) * (z.im : ℂ) ^ k * ((z.im : ℂ) ^ 2)⁻¹ =
        4 * (Real.pi : ℂ) * Complex.I ^ k / (((k : ℂ) - 1) * 2 ^ k) * f w := by
  exact UploadBergman.main k hk f hf C hC w hw
