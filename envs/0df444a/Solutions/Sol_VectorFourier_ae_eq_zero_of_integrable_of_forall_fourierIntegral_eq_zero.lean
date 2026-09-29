-- Prove2me | solution 1 for VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6321910a-79c9-5d23-9fce-5cdf0aae4878

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
import Theorems.Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (f : V → ℂ) (_hf : Integrable f μ)
    (_h : ∀ w : V, VectorFourier.fourierIntegral 𝐞 μ B f w = 0) :
    f =ᵐ[μ] 0 := by
  classical

  set n : ℕ := Module.finrank ℝ V with hn
  let b : Module.Basis (Fin n) ℝ V := Module.finBasis ℝ V

  have hL : Continuous fun p : V × V => B p.1 p.2 := by
    let B₂ : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ B)
    have hB₂ : ∀ p : V × V, B₂ p.1 p.2 = B p.1 p.2 := fun p => rfl
    exact B₂.continuous₂

  have hdet : (Matrix.of fun i j => B (b i) (b j)).det ≠ 0 := by
    have h1 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 _hB
    have h2 : (Matrix.of fun i j => B (b i) (b j)) = LinearMap.BilinForm.toMatrix b B := by
      ext i j
      rw [Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply]
    rw [h2]
    exact h1
  have hvol : μ.real (ZSpan.fundamentalDomain b) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b)
      (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne).ne'
  set cB : ℝ := (μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| with hcB
  have hcB0 : cB ≠ 0 := div_ne_zero (pow_ne_zero 2 hvol) (abs_ne_zero.2 hdet)

  have key : ∀ g : 𝓢(V, ℂ), ∫ x, f x * VectorFourier.fourierIntegral 𝐞 μ (LinearMap.flip B) g x ∂μ = 0 := by
    intro g
    have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := B) (μ := μ) (ν := μ) (e := 𝐞)
      (f := f) (g := (⇑g : V → ℂ)) Real.continuous_fourierChar hL _hf g.integrable
    simp only [_h, smul_eq_mul, zero_mul, integral_zero] at hflip
    exact hflip.symm

  have htest : ∀ G : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → ∫ x, f x * G x ∂μ = 0 := by
    intro G hGd hGs

    have hGd' : ContDiff ℝ (⊤ : ℕ∞) (fun x => G (-x)) := hGd.comp contDiff_neg
    have hGs' : HasCompactSupport (fun x => G (-x)) := hGs.comp_homeomorph (Homeomorph.neg V)
    set Gr : 𝓢(V, ℂ) := hGs'.toSchwartzMap hGd' with hGr
    have hGr_apply : ∀ x, Gr x = G (-x) := fun x => rfl

    obtain ⟨H, hH⟩ := SchwartzMap.exists_coe_eq_vectorFourierIntegral μ B _hB Gr

    have hinv : ∀ x, VectorFourier.fourierIntegral 𝐞 μ (LinearMap.flip B) (⇑H) x = (cB : ℂ) * G x := by
      intro x
      have e := VectorFourier.fourierIntegral_flip_fourierIntegral_eq μ B _hB b Gr x
      rw [hGr_apply, neg_neg, ← hcB] at e
      rw [hH]
      exact e
    have h0 := key H
    simp_rw [hinv] at h0
    have h1 : ∫ x, f x * ((cB : ℂ) * G x) ∂μ = (cB : ℂ) * ∫ x, f x * G x ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Complex.ofReal_ne_zero.2 hcB0)

  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := μ) _hf.locallyIntegrable fun g hgd hgs => by
    have hG := htest (fun x => (g x : ℂ)) (Complex.ofRealCLM.contDiff.comp hgd)
      (hgs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    rw [← hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (g x : ℂ) • f x = f x * (g x : ℂ)
    rw [smul_eq_mul, mul_comm]
  exact hae

end S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
end P2MW
export P2MW.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero (solution)
