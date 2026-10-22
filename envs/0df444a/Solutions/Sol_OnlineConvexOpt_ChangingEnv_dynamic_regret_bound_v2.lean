-- Prove2me | solution 1 for OnlineConvexOpt.ChangingEnv.dynamic_regret_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:58:31.757506+00:00
-- url     : https://prove2.me/submissions/964e4398-cd72-4bd8-bdad-fa3bd83c6c04

-- SPDX-License-Identifier: Apache-2.0
-- The convex support, projection, and one-step OGD helpers are adapted from
-- arexychen, Prove2Me submission 5ad709c6-386c-41d2-81ca-ff1585096347.
-- The moving-comparator estimate and dynamic telescoping argument follow
-- Hazan, Introduction to Online Convex Optimization, 2nd ed., Theorem 10.1.
import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2
open OnlineConvexOpt.FirstOrder OnlineConvexOpt.ChangingEnv Finset
open scoped RealInnerProductSpace

namespace P2MDynamicOGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma convex_support {K : Set E} {f : E → ℝ} {x y : E} {L : E →L[ℝ] ℝ}
    (hf : ConvexOn ℝ K f) (hx : x ∈ K) (hy : y ∈ K)
    (hd : HasFDerivAt f L x) : L (y - x) ≤ f y - f x := by
  have hc := hf.comp_affineMap (AffineMap.lineMap x y)
  have hd' : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) (L (y - x)) (0 : ℝ) := by
    apply hd.comp_hasDerivAt_of_eq 0 AffineMap.hasDerivAt_lineMap
    simp
  have hh := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa using hx) (by simpa using hy) (by norm_num) hd'
  simpa [slope_def_field] using hh

lemma gradient_support {K : Set E} {f : E → ℝ} {x y g : E}
    (hf : ConvexOn ℝ K f) (hx : x ∈ K) (hy : y ∈ K)
    (hd : HasGradientAt f g x) : f x - f y ≤ ⟪g, x - y⟫ := by
  have h := convex_support hf hx hy hd.hasFDerivAt
  change ⟪g, y - x⟫ ≤ f y - f x at h
  simp only [inner_sub_right] at h ⊢
  linarith

lemma projection_sq {K : Set E} (hc : Convex ℝ K) {v p y : E}
    (hp : IsMetricProjection K v p) (hy : y ∈ K) : ‖p - y‖ ^ 2 ≤ ‖v - y‖ ^ 2 := by
  letI : Nonempty K := ⟨⟨p, hp.1⟩⟩
  have he : ‖v - p‖ = ⨅ z : K, ‖v - z‖ := by
    apply le_antisymm
    · exact le_ciInf (fun z => by simpa only [dist_eq_norm] using hp.2 z z.property)
    · exact ciInf_le (show BddBelow (Set.range (fun z : K => ‖v - z‖)) from
        ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩) ⟨p, hp.1⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hp.1).mp he y hy
  have hn := sq_nonneg ‖v - p‖
  have heq : v - y = (v - p) - (y - p) := by abel
  rw [heq, norm_sub_sq_real (v - p) (y - p), norm_sub_rev p y]
  linarith

lemma step_inner {K : Set E} (hc : Convex ℝ K) {x xn g y : E} {η G : ℝ}
    (hp : IsMetricProjection K (x - η • g) xn) (hy : y ∈ K)
    (hη : 0 < η) (hG : ‖g‖ ≤ G) :
    ⟪g, x - y⟫ ≤ (‖x - y‖ ^ 2 - ‖xn - y‖ ^ 2) / (2 * η) + η / 2 * G ^ 2 := by
  have h := projection_sq hc hp hy
  have heq : x - η • g - y = (x - y) - η • g := by abel
  rw [heq, norm_sub_sq_real (x - y) (η • g), inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, mul_pow, real_inner_comm g (x - y)] at h
  have hg2 : ‖g‖ ^ 2 ≤ G ^ 2 := sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hG) |>.2 hG
  have he : (‖x - y‖ ^ 2 - ‖xn - y‖ ^ 2) / (2 * η) + η / 2 * G ^ 2 =
      (‖x - y‖ ^ 2 - ‖xn - y‖ ^ 2 + η ^ 2 * G ^ 2) / (2 * η) := by
    field_simp
    <;> ring
  rw [he]
  apply (le_div_iff₀ (show 0 < 2 * η by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hg2 (sq_nonneg η)]

lemma ogd_mem {K : Set E} {f : ℕ → E → ℝ} {η : ℕ → ℝ} {x g : ℕ → E}
    (h : IsOnlineGradientDescent K f η x g) (t : ℕ) : x t ∈ K := by
  cases t with
  | zero => exact h.1
  | succ t => exact (h.2 t).2.1

end P2MDynamicOGD

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (η : ℝ) (hηpos : 0 < η)
    (u : ℕ → E) (hu : ∀ t, u t ∈ K)
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f (fun _ => η) x g)
    (T : ℕ) (hT : 1 ≤ T) :
    DynamicRegretT f x u T ≤
      (D ^ 2 + 2 * D * ∑ t ∈ Finset.range (T - 1), ‖u t - u (t + 1)‖) / (2 * η) +
        (η / 2) * G ^ 2 * T  := by
  classical
  have hx (t : ℕ) : x t ∈ K := P2MDynamicOGD.ogd_mem hOGD t
  have hnorm (s t : ℕ) : ‖x s - u t‖ ≤ D := by
    simpa only [dist_eq_norm] using hD (x s) (hx s) (u t) (hu t)
  have hmove (t : ℕ) :
      ‖x (t+1)-u (t+1)‖^2 - ‖x (t+1)-u t‖^2 ≤
        2*D*‖u t-u (t+1)‖ := by
    have hd := norm_sub_norm_le (x (t+1)-u (t+1)) (x (t+1)-u t)
    have he : (x (t+1)-u (t+1))-(x (t+1)-u t) = u t-u (t+1) := by abel
    rw [he] at hd
    have hs : 0 ≤ ‖x (t+1)-u (t+1)‖+‖x (t+1)-u t‖ := by positivity
    have hp := mul_le_mul_of_nonneg_right hd hs
    have hb := mul_le_mul_of_nonneg_left
      (show ‖x (t+1)-u (t+1)‖+‖x (t+1)-u t‖ ≤ 2*D by
        linarith [hnorm (t+1) (t+1), hnorm (t+1) t])
      (norm_nonneg (u t-u (t+1)))
    nlinarith
  let a : ℕ → ℝ := fun t => ‖x t-u t‖^2 - ‖x (t+1)-u t‖^2
  have htel (n : ℕ) : (∑ t ∈ range (n+1), a t) ≤
      ‖x 0-u 0‖^2 + 2*D*(∑ t ∈ range n, ‖u t-u (t+1)‖) -
        ‖x (n+1)-u n‖^2 := by
    induction n with
    | zero => simp [a]
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ (f := fun t => ‖u t-u (t+1)‖)]
      have hm := hmove n
      dsimp [a]
      dsimp [a] at ih
      linarith
  have hinit : ‖x 0-u 0‖^2 ≤ D^2 :=
    (sq_le_sq₀ (norm_nonneg _) hDpos.le).2 (hnorm 0 0)
  have ht := htel (T-1)
  rw [Nat.sub_add_cancel hT] at ht
  have htel' : (∑ t ∈ range T, a t) ≤
      D^2+2*D*(∑ t ∈ range (T-1), ‖u t-u (t+1)‖) := by
    nlinarith [sq_nonneg ‖x T-u (T-1)‖]
  have hstep (t : ℕ) : f t (x t)-f t (u t) ≤ a t/(2*η)+η/2*G^2 := by
    have hg := hfG t (x t) (hx t) (g t) (hOGD.2 t).1
    exact (P2MDynamicOGD.gradient_support (hfconv t) (hx t) (hu t) (hOGD.2 t).1).trans
      (P2MDynamicOGD.step_inner hKconv (hOGD.2 t).2 (hu t) hηpos hg)
  have hsum := sum_le_sum (fun t (_ : t ∈ range T) => hstep t)
  rw [sum_sub_distrib, sum_add_distrib, ← sum_div] at hsum
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have hdiv := div_le_div_of_nonneg_right htel' (show 0 ≤ 2*η by positivity)
  unfold DynamicRegretT
  nlinarith
