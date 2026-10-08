-- Prove2me | solution 1 for OnlineConvexOpt.FirstOrder.online_gradient_descent_strongly_convex_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:58:15.817895+00:00
-- url     : https://prove2.me/submissions/315741c0-18ff-47b9-9c45-c293ab034cc6

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2


open OnlineConvexOpt.FirstOrder
open scoped RealInnerProductSpace
open Finset

namespace OGDProof

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

lemma strong_support {K : Set E} {f : E → ℝ} {x y g : E} {α : ℝ}
    (hf : StrongConvexOn K α f) (hx : x ∈ K) (hy : y ∈ K)
    (hd : HasGradientAt f g x) :
    f x - f y ≤ ⟪g, x - y⟫ - α / 2 * ‖x - y‖ ^ 2 := by
  have hc := strongConvexOn_iff_convex.mp hf
  have hd' := hd.hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (α / 2))
  have h := convex_support hc hx hy hd'
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  change ⟪g, y - x⟫ - α / 2 * (2 * ⟪x, y - x⟫) ≤
    (f y - α / 2 * ‖y‖ ^ 2) - (f x - α / 2 * ‖x‖ ^ 2) at h
  simp only [inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real, inner_sub_right]
  nlinarith

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

lemma regret_of_comparator {K : Set E} {f : ℕ → E → ℝ} {x : ℕ → E} {T : ℕ} {B : ℝ}
    (hne : K.Nonempty)
    (h : ∀ y ∈ K, (∑ t ∈ range T, f t (x t)) - ∑ t ∈ range T, f t y ≤ B) :
    RegretT K f x T ≤ B := by
  unfold RegretT
  have hl : (∑ t ∈ range T, f t (x t)) - B ≤
      sInf ((fun y => ∑ t ∈ range T, f t y) '' K) := by
    apply le_csInf (hne.image _)
    rintro _ ⟨y, hy, rfl⟩
    linarith [h y hy]
  linarith

end OGDProof

open Finset

namespace OGDProof

lemma weighted_telescope (a w : ℕ → ℝ) (B : ℝ)
    (hw0 : w 0 = 0) (hw : Monotone w) (ha : ∀ n, a n ≤ B) (N : ℕ) :
    ∑ t ∈ range N, w (t + 1) * (a t - a (t + 1)) ≤ w N * B - w N * a N := by
  induction N with
  | zero => simp [hw0]
  | succ N ih =>
    rw [sum_range_succ]
    have hprod := mul_nonneg (sub_nonneg.mpr (hw (Nat.le_succ N))) (sub_nonneg.mpr (ha N))
    nlinarith

lemma inv_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hp : (0 : ℝ) < n + 1 := by positivity
  have hb := Real.sqrt_pos.2 hp
  have hab : Real.sqrt n ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt (by linarith)
  have ha2 := Real.sq_sqrt hn
  have hb2 := Real.sq_sqrt hp.le
  apply (div_le_iff₀ hb).2
  have hmul := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab)
  nlinarith

lemma sum_inv_sqrt (N : ℕ) :
    ∑ t ∈ range N, (1 / Real.sqrt (t + 1)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h := inv_sqrt_step N
    push_cast
    linarith

lemma sum_inv_nat (N : ℕ) :
    ∑ t ∈ range N, (1 / ((t : ℝ) + 1)) ≤ 1 + Real.log N := by
  have he : (∑ t ∈ range N, (1 / ((t : ℝ) + 1))) = (harmonic N : ℝ) := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, one_div]
  rw [he]
  exact harmonic_le_one_add_log N

end OGDProof

open OnlineConvexOpt.FirstOrder OGDProof
open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem solution (K : Set E) (G : ℝ) (f : ℕ → E → ℝ)
    (hKconv : Convex ℝ K) (hKcomplete : IsComplete K) (hKne : K.Nonempty) (hGpos : 0 < G)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hG : ∀ t, ∀ x ∈ K, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (α : ℝ) (hα : 0 < α) (hfSC : ∀ t, StrongConvexOn K α (f t))
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, η t = 1 / (α * (t + 1)))
    (x g : ℕ → E) (hOGD : IsOnlineGradientDescent K f η x g)
    (T : ℕ) (hT : 1 ≤ T) :
    RegretT K f x T ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T) := by
  apply regret_of_comparator hKne
  intro y hy
  let a : ℕ → ℝ := fun t => ‖x t - y‖ ^ 2
  have hs (t : ℕ) : f t (x t) - f t y ≤
      α / 2 * ((t : ℝ) * a t - (t + 1) * a (t + 1)) +
        G ^ 2 / (2 * α) * (1 / ((t : ℝ) + 1)) := by
    have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hηpos : 0 < η t := by rw [hη]; positivity
    have hi := step_inner hKconv (hOGD.2 t).2 hy hηpos
      (hG t (x t) (ogd_mem hOGD t) (g t) (hOGD.2 t).1)
    have hc := strong_support (hfSC t) (ogd_mem hOGD t) hy (hOGD.2 t).1
    have hstep : f t (x t) - f t y ≤
        (a t - a (t + 1)) / (2 * η t) + η t / 2 * G ^ 2 - α / 2 * a t := by
      dsimp [a]
      linarith
    apply hstep.trans_eq
    rw [hη]
    field_simp
    <;> ring
  have hsum := sum_le_sum (fun t (_ : t ∈ range T) => hs t)
  have htel : (∑ t ∈ range T, α / 2 * ((t : ℝ) * a t - (t + 1) * a (t + 1))) =
      -(α / 2 * T * a T) := by
    have he : ∀ t : ℕ, α / 2 * ((t : ℝ) * a t - (t + 1) * a (t + 1)) =
        (α / 2 * t * a t) - (α / 2 * (t + 1) * a (t + 1)) := by intro t; ring
    simp_rw [he]
    have h := sum_range_sub (fun t => α / 2 * (t : ℝ) * a t) T
    simp only [sum_sub_distrib, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      mul_zero, zero_mul, sub_zero] at h ⊢
    linarith
  rw [sum_sub_distrib, sum_add_distrib, htel, ← mul_sum] at hsum
  have hn : 0 ≤ α / 2 * T * a T := by dsimp [a]; positivity
  have hh := mul_le_mul_of_nonneg_left (sum_inv_nat T)
    (show 0 ≤ G ^ 2 / (2 * α) by positivity)
  linarith

#print axioms solution
