-- Prove2me | solution 1 for StochCoordProx.lemma_1_descent_along_U
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-31T12:19:20.624289+00:00
-- url     : https://prove2.me/submissions/754aa8ab-8343-4abb-bb91-da62ae1776cd

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_StochCoordProx_IsSmoothAlong

open Matrix Set
open scoped InnerProductSpace

private lemma d31_real_remainder (g g' : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (g' t) t)
    (hbound : ∀ t, 0 ≤ t → |g' t - g' 0| ≤ L * t) :
    |g 1 - g 0 - g' 0| ≤ L / 2 := by
  let u : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 - L / 2 * t ^ 2
  let l : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 + L / 2 * t ^ 2
  have hu (t : ℝ) : HasDerivAt u (g' t - g' 0 - L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [u, id]) <;> ring
  have hl (t : ℝ) : HasDerivAt l (g' t - g' 0 + L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).add
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [l, id]) <;> ring
  have hanti : AntitoneOn u (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hu t).continuousAt.continuousWithinAt)
      (fun t _ => (hu t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hu t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).2
    linarith
  have hmono : MonotoneOn l (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hl t).continuousAt.continuousWithinAt)
      (fun t _ => (hl t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hl t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).1
    linarith
  have hu01 := hanti (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  have hl01 := hmono (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  dsimp [u, l] at hu01 hl01
  apply abs_le.mpr
  constructor <;> linarith

private lemma d31_transpose_inner {n p : ℕ} (U : Matrix (Fin n) (Fin p) ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin p)) :
    ⟪Matrix.toEuclideanLin Uᵀ a, b⟫_ℝ = ⟪a, Matrix.toEuclideanLin U b⟫_ℝ := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h]
  exact LinearMap.adjoint_inner_left _ _ _

private lemma d31_smooth_descent {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin p) ℝ) (LU : ℝ) (hf : Differentiable ℝ f)
    (hL : StochCoordProx.IsSmoothAlong f U LU)
    (x : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin p)) :
    |f (x + Matrix.toEuclideanLin U h) - f x - ⟪Matrix.toEuclideanLin Uᵀ (gradient f x), h⟫_ℝ| ≤
      LU / 2 * ‖h‖ ^ 2 := by
  let g : ℝ → ℝ := fun t => f (x + t • Matrix.toEuclideanLin U h)
  let g' : ℝ → ℝ := fun t =>
    ⟪Matrix.toEuclideanLin Uᵀ (gradient f (x + t • Matrix.toEuclideanLin U h)), h⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (g' t) t := by
    have hp : HasDerivAt (fun s : ℝ => x + s • Matrix.toEuclideanLin U h)
        (Matrix.toEuclideanLin U h) t := by
      simpa using ((hasDerivAt_id t).smul_const (Matrix.toEuclideanLin U h)).const_add x
    have hc := (hf (x + t • Matrix.toEuclideanLin U h)).hasFDerivAt.comp_hasDerivAt t hp
    convert! hc using 1
    simp only [g', d31_transpose_inner, inner_gradient_left]
  have hb (t : ℝ) (ht : 0 ≤ t) : |g' t - g' 0| ≤ (LU * ‖h‖ ^ 2) * t := by
    have hproj := hL x (t • h)
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hproj
    dsimp [g']
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left, ← map_sub]
    calc
      _ ≤ ‖Matrix.toEuclideanLin Uᵀ
          (gradient f (x + t • Matrix.toEuclideanLin U h) - gradient f x)‖ * ‖h‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (LU * (t * ‖h‖)) * ‖h‖ := mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = (LU * ‖h‖ ^ 2) * t := by ring
  have hr := d31_real_remainder g g' (LU * ‖h‖ ^ 2) hd hb
  simpa [g, g', mul_div_assoc, div_mul_eq_mul_div] using hr

theorem solution {n p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin p) ℝ) (LU : ℝ) (hf : Differentiable ℝ f)
    (hL : StochCoordProx.IsSmoothAlong f U LU) (x : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin p)) :
    |f (x + Matrix.toEuclideanLin U h) - f x - ⟪Matrix.toEuclideanLin Uᵀ (gradient f x), h⟫_ℝ| ≤
      LU / 2 * ‖h‖ ^ 2 := by
  exact d31_smooth_descent f U LU hf hL x h

#print axioms solution
