-- Prove2me | solution 1 for RetailVariety.Structure.mangasarian_ratio_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:20:32.88898+00:00
-- url     : https://prove2.me/submissions/2a87d897-b82f-4e25-bbe5-b65d78ab9551

import Mathlib

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E)
    (g f : E → ℝ) (hg : ConvexOn ℝ X g) (hf_pos : ∀ x ∈ X, 0 < f x)
    (hf_lin : ConvexOn ℝ X f ∧ ConcaveOn ℝ X f) :
    QuasiconvexOn ℝ X (fun x => g x / f x) := by
  intro r
  intro x hx y hy a b ha hb hab
  have hz := hg.1 hx.1 hy.1 ha hb hab
  refine ⟨hz, ?_⟩
  have hfx := hf_pos x hx.1
  have hfy := hf_pos y hy.1
  have hxy := hg.2 hx.1 hy.1 ha hb hab
  have hf1 := hf_lin.1.2 hx.1 hy.1 ha hb hab
  have hf2 := hf_lin.2.2 hx.1 hy.1 ha hb hab
  have he : f (a • x + b • y) = a * f x + b * f y := by
    simpa only [smul_eq_mul] using le_antisymm hf1 hf2
  have hx' := (div_le_iff₀ hfx).mp hx.2
  have hy' := (div_le_iff₀ hfy).mp hy.2
  apply (div_le_iff₀ (hf_pos _ hz)).mpr
  rw [he]
  have hax := mul_le_mul_of_nonneg_left hx' ha
  have hby := mul_le_mul_of_nonneg_left hy' hb
  simp only [smul_eq_mul] at hxy
  nlinarith

#print axioms solution
