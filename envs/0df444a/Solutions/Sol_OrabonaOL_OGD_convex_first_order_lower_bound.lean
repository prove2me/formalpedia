-- Prove2me | solution 1 for OrabonaOL.OGD.convex_first_order_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:24:29.834805+00:00
-- url     : https://prove2.me/submissions/cb40ce3b-3f34-46b2-b536-b8e9d4397a7d

import Mathlib

theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ S f)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) (hdiff : DifferentiableAt ℝ f x) :
    ∀ y ∈ S, f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  intro y hy
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d))) := by
    have h := hf.comp_affineMap ((AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d)))
    refine h.subset ?_ (convex_Icc 0 1)
    intro t ht
    exact hf.1.lineMap_mem hx hy ht
  have hd : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d))) (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d)) (y - x) (0 : ℝ) := AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f (fderiv ℝ f x) ((AffineMap.lineMap x y : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin d)) (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]
      exact hdiff.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hs := hconv.le_slope_of_hasDerivAt ⟨le_refl (0 : ℝ), zero_le_one⟩
    ⟨zero_le_one, le_refl (1 : ℝ)⟩ zero_lt_one hd
  rw [slope_def_field] at hs
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at hs
  have hg : inner ℝ (gradient f x) (y - x) = fderiv ℝ f x (y - x) := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  linarith
