-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.comonotone_covariance_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:05:47.92306+00:00
-- url     : https://prove2.me/submissions/34b524bc-ceea-48c2-803a-0484f4549ace

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem solution {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x*g x) μ)
    (hmono : ∀ x y, 0 ≤ (f x-f y)*(g x-g y)) :
    (∫ x, f x ∂μ)*(∫ x, g x ∂μ) ≤ ∫ x, f x*g x ∂μ := by
  let F11 : X × X → ℝ := fun p => f p.1*g p.1
  let F12 : X × X → ℝ := fun p => f p.1*g p.2
  let F21 : X × X → ℝ := fun p => f p.2*g p.1
  let F22 : X × X → ℝ := fun p => f p.2*g p.2
  have h11 : Integrable F11 (μ.prod μ) := hfg.comp_fst μ
  have h12 : Integrable F12 (μ.prod μ) := hf.mul_prod hg
  have h21 : Integrable F21 (μ.prod μ) := (hg.mul_prod hf).congr (by filter_upwards with p; dsimp [F21]; ring)
  have h22 : Integrable F22 (μ.prod μ) := hfg.comp_snd μ
  have hi11 : (∫ p, F11 p ∂(μ.prod μ)) = ∫ x, f x*g x ∂μ := by
    rw [integral_prod _ h11]
    simp [F11]
  have hi22 : (∫ p, F22 p ∂(μ.prod μ)) = ∫ x, f x*g x ∂μ := by
    rw [integral_prod_symm _ h22]
    simp [F22]
  have hi12 : (∫ p, F12 p ∂(μ.prod μ)) = (∫ x, f x ∂μ)*(∫ x, g x ∂μ) :=
    integral_prod_mul f g
  have hi21 : (∫ p, F21 p ∂(μ.prod μ)) = (∫ x, f x ∂μ)*(∫ x, g x ∂μ) := by
    calc
      _ = ∫ p, g p.1*f p.2 ∂(μ.prod μ) := by apply integral_congr_ae; filter_upwards with p; dsimp [F21]; ring
      _ = (∫ x, g x ∂μ)*(∫ x, f x ∂μ) := integral_prod_mul g f
      _ = _ := by ring
  have hpoint : 0 ≤ᵐ[μ.prod μ] (fun p => F11 p-F12 p-F21 p+F22 p) := by
    filter_upwards with p
    have hh := hmono p.1 p.2
    dsimp [F11,F12,F21,F22]
    nlinarith [hh]
  have h := integral_nonneg_of_ae hpoint
  have ha := integral_add ((h11.sub h12).sub h21) h22
  have hb := integral_sub (h11.sub h12) h21
  have hc := integral_sub h11 h12
  simp only [Pi.add_apply,Pi.sub_apply] at ha hb hc
  rw [ha,hb,hc,hi11,hi12,hi21,hi22] at h
  linarith
