-- Prove2me | solution 1 for OnlineConvexOpt.ProjectionFree.cg_convergence_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:21:17.995451+00:00
-- url     : https://prove2.me/submissions/8db3dd8e-5d04-4b77-b666-465ff0b316a8

import Mathlib
import Definitions.Def_OnlineConvexOpt_ProjectionFree_ConditionalGradient
import Definitions.Def_OnlineConvexOpt_ProjectionFree_SmoothOn

open scoped InnerProductSpace

namespace OnlineConvexOpt.ProjectionFree

lemma cgc_grad_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (f : E → ℝ) (hfconv : ConvexOn ℝ K f) (gx x y : E) (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientAt f gx x) : f x + ⟪gx, y - x⟫_ℝ ≤ f y := by
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hL
  have e : ∀ s : ℝ, L s = x + s • (y - x) := by
    intro s; rw [hL, AffineMap.lineMap_apply_module']; abel
  have hc : ConvexOn ℝ (L ⁻¹' K) (fun s : ℝ => f (x + s • (y - x))) := by
    have h := hfconv.comp_affineMap L
    have heq : (f ∘ L) = fun s : ℝ => f (x + s • (y - x)) := by funext s; simp [e]
    rw [heq] at h; exact h
  have hd : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hd2 : HasDerivAt (fun s : ℝ => f (x + s • (y - x))) ⟪gx, y - x⟫_ℝ 0 := by
    have h1 := hg.hasFDerivAt
    have h1' : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) gx) (x + (0:ℝ) • (y - x)) := by
      simpa using h1
    have := h1'.comp_hasDerivAt (0:ℝ) hd
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have h0 : (0:ℝ) ∈ L ⁻¹' K := by simp [e, hx]
  have h1 : (1:ℝ) ∈ L ⁻¹' K := by simp [e, hy]
  have := hc.le_slope_of_hasDerivAt h0 h1 zero_lt_one hd2
  simp [slope] at this
  linarith

theorem cgc_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K)
    (D : ℝ) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (hg : ∀ x ∈ K, HasGradientAt f (g x) x)
    (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by
  obtain ⟨hx1, hstep⟩ := hrun
  have hη01 : ∀ t : ℕ, 1 ≤ t → 0 ≤ η t ∧ η t ≤ 1 := by
    intro t ht
    rw [hη t ht]
    exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  have hxK : ∀ t : ℕ, 1 ≤ t → x t ∈ K := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hx1
    | succ n hn ih =>
      rw [(hstep n hn).2]
      exact hKconv.add_smul_sub_mem ih (hstep n hn).1.1 (hη01 n hn)
  -- recursion
  have hrec : ∀ t : ℕ, 1 ≤ t → f (x (t+1)) - f xstar ≤
      (1 - η t) * (f (x t) - f xstar) + β / 2 * η t ^ 2 * D ^ 2 := by
    intro t ht
    obtain ⟨⟨hvK, hvmin⟩, hxs⟩ := hstep t ht
    have hxt := hxK t ht
    have hsm := hsmooth (x t) hxt (x (t+1)) (hxK (t+1) (by omega))
    rw [hxs, add_sub_cancel_left, inner_smul_right, norm_smul,
      Real.norm_of_nonneg (hη01 t ht).1] at hsm
    have hgi := cgc_grad_ineq K f hfconv (g (x t)) (x t) xstar hxt hxstar (hg _ hxt)
    have hlo := hvmin xstar hxstar
    have e1 : ⟪g (x t), v t - x t⟫_ℝ ≤ f xstar - f (x t) := by
      rw [inner_sub_right] at hgi ⊢; linarith
    have hdist : ‖v t - x t‖ ≤ D := by rw [← dist_eq_norm]; exact hD _ hvK _ hxt
    have hn0 : 0 ≤ ‖v t - x t‖ := norm_nonneg _
    have hsq : ‖v t - x t‖ ^ 2 ≤ D ^ 2 := by nlinarith
    obtain ⟨h0, h1⟩ := hη01 t ht
    have a1 : η t * ⟪g (x t), v t - x t⟫_ℝ ≤ η t * (f xstar - f (x t)) :=
      mul_le_mul_of_nonneg_left e1 h0
    rw [hxs]
    have a2 : β / 2 * (η t * ‖v t - x t‖) ^ 2 ≤ β / 2 * η t ^ 2 * D ^ 2 := by
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith
  induction t, ht using Nat.le_induction with
  | base =>
    have h := hrec 1 le_rfl
    rw [hη 1 le_rfl] at h
    norm_num at h ⊢
    nlinarith [sq_nonneg D]
  | succ n hn ih =>
    have h := hrec n (by omega)
    rw [hη n (by omega)] at h
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    have hmin : min 1 (2 / (n:ℝ)) = 2 / n := by
      apply min_eq_right; rw [div_le_one (by linarith)]; exact hn2
    rw [hmin] at h
    have hc : 0 ≤ 1 - 2 / (n:ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hn2
    have h2 := mul_le_mul_of_nonneg_left ih hc
    push_cast
    have hB : 0 ≤ β * D ^ 2 := by positivity
    have key : (1 - 2 / (n:ℝ)) * (2 * β * D ^ 2 / n) + β / 2 * (2 / (n:ℝ)) ^ 2 * D ^ 2 ≤
        2 * β * D ^ 2 / ((n:ℝ) + 1) := by
      have e : (1 - 2 / (n:ℝ)) * (2 * β * D ^ 2 / n) + β / 2 * (2 / (n:ℝ)) ^ 2 * D ^ 2
          = 2 * (β * D ^ 2) * ((n:ℝ) - 1) / n ^ 2 := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have : ((n:ℝ) - 1) * ((n:ℝ) + 1) ≤ (n:ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
end OnlineConvexOpt.ProjectionFree

open OnlineConvexOpt.ProjectionFree


theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : E → ℝ) (g : E → E) (hg : ∀ x ∈ K, HasGradientAt f (g x) x)
    (β : ℝ) (hβpos : 0 < β) (hsmooth : SmoothOn K f g β)
    (hfconv : ConvexOn ℝ K f)
    (xstar : E) (hxstar : xstar ∈ K) (hxstar_min : ∀ x ∈ K, f xstar ≤ f x)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η t = min 1 (2 / (t : ℝ)))
    (x v : ℕ → E) (hrun : IsConditionalGradientRun K g η x v)
    (t : ℕ) (ht : 2 ≤ t) :
    f (x t) - f xstar ≤ 2 * β * D ^ 2 / t := by
  exact cgc_core K hKconv D hD f g hg β hβpos hsmooth hfconv xstar hxstar hxstar_min η hη x v hrun t ht
