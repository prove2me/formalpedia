-- Prove2me | solution 1 for TwoAssumptions.prop7_conjugate_pair
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:28.158618+00:00
-- url     : https://prove2.me/submissions/1492c00f-2a95-4932-94a9-840018e5f411

import Mathlib
open scoped ContDiff
namespace TwoAssumptions

theorem _root_.solution (f : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ)
    (hf : ContDiffAt ℝ 1 f x)
    (hq : fderiv ℝ (fun qk => (f qk).1) x (0, 1) = 0)
    (hJ : |(fderiv ℝ f x).det| = 1) :
    |fderiv ℝ (fun qk => (f qk).2) x (0, 1)| =
      |fderiv ℝ (fun qk => (f qk).1) x (1, 0)|⁻¹ := by
  have hd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun qk => (f qk).1) x = (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ f x) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp x hd.hasFDerivAt |>.fderiv
  have h2 : fderiv ℝ (fun qk => (f qk).2) x = (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ f x) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp x hd.hasFDerivAt |>.fderiv
  rw [h1, h2]; rw [h1] at hq
  set L := fderiv ℝ f x with hL
  have hdet : L.det = (L (1,0)).1 * (L (0,1)).2 - (L (0,1)).1 * (L (1,0)).2 := by
    show LinearMap.det (L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) = _
    rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
  have hq' : (L (0,1)).1 = 0 := hq
  rw [hdet, hq', zero_mul, sub_zero, abs_mul] at hJ
  show |(L (0,1)).2| = |(L (1,0)).1|⁻¹
  exact eq_inv_of_mul_eq_one_right hJ


end TwoAssumptions
