-- Prove2me | solution 1 for SAGA.StronglyConvex.corollary1_linear_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:00:58.646778+00:00
-- url     : https://prove2.me/submissions/f2f9bd06-fc46-47c3-980a-355f45aefb0c

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_SAGA_StronglyConvex_sagaStep
import Definitions.Def_SAGA_StronglyConvex_lyapunov
import Definitions.Def_SAGA_StronglyConvex_sagaRun

open scoped InnerProductSpace
open scoped RealInnerProductSpace

namespace SAGA.StronglyConvex

lemma sg_line {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (g' : EuclideanSpace ℝ (Fin d))
    (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) (hg : HasGradientAt g g' (x + t • v)) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) ⟪g', v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := hg.hasFDerivAt.comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at this
  exact this

lemma sg_strong_lower {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (μ : ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : StrongConvexOn Set.univ μ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ + μ / 2 * ‖w - x‖ ^ 2 ≤ g w := by
  set r := w - x with hr
  have hφ := strongConvexOn_iff_convex.mp hconv
  set ψ : ℝ → ℝ := fun s => g (x + s • r) - μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2)
    with hψ
  have hψeq : ∀ s : ℝ, ψ s = g (x + s • r) - μ / (2:ℝ) * ‖x + s • r‖ ^ 2 := by
    intro s
    simp only [hψ]
    rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ p q hp hq hpq
    have e : x + (p • a + q • b) • r = p • (x + a • r) + q • (x + b • r) := by
      obtain rfl : q = 1 - p := by linarith
      simp only [smul_eq_mul]
      module
    rw [hψeq, hψeq, hψeq, e]
    exact hφ.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have hd1 : HasDerivAt (fun s : ℝ => g (x + s • r)) ⟪g', r⟫ 0 :=
    sg_line g g' x r 0 (by simpa using hgrad)
  have hd2 : HasDerivAt (fun s : ℝ => μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2))
      (μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s * ⟪x, r⟫) (2 * ⟪x, r⟫) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ⟪x, r⟫
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * ‖r‖ ^ 2) (2 * 0 * ‖r‖ ^ 2) 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const (‖r‖ ^ 2)
    exact (((hasDerivAt_const (0:ℝ) (‖x‖ ^ 2)).add h1).add h2).const_mul (μ / 2) |>.congr_deriv
      (by ring)
  have hd : HasDerivAt ψ (⟪g', r⟫ - μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := hd1.sub hd2
  have hs := hψconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    zero_lt_one hd
  rw [slope_def_field] at hs
  simp only [hψ] at hs
  have e1 : x + (1:ℝ) • r = w := by simp [hr]
  have e0 : x + (0:ℝ) • r = x := by simp
  rw [e1, e0] at hs
  norm_num at hs
  nlinarith

lemma sg_grad_ineq {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexOn ℝ Set.univ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ ≤ g w := by
  have := sg_strong_lower g 0 g' x w (strongConvexOn_zero.mpr hconv) hgrad
  simpa using this

lemma sg_descent {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ x, HasGradientAt g (g' x) x) (L : ℝ)
    (hL : ∀ x y, ‖g' x - g' y‖ ≤ L * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin d)) :
    g y ≤ g x + ⟪g' x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => g (x + t • v) - t * ⟪g' x, v⟫ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪g' (x + t • v), v⟫ - ⟪g' x, v⟫ - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := sg_line g (g' (x + t • v)) x v t (hgrad _)
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪g' x, v⟫) ⟪g' x, v⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g' x, v⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : ⟪g' (x + t • v) - g' x, v⟫ ≤
          ‖g' (x + t • v) - g' x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL (x + t • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

/-- generalized cocoercivity, multiplied form. -/
lemma sg_cocoer {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (μ L : ℝ)
    (hlow : ∀ x w, g x + ⟪g' x, w - x⟫ + μ / 2 * ‖w - x‖ ^ 2 ≤ g w)
    (hup : ∀ x w, g w ≤ g x + ⟪g' x, w - x⟫ + L / 2 * ‖w - x‖ ^ 2)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖g' y - g' x - μ • (y - x)‖ ^ 2 ≤
      2 * (L - μ) * (g y - g x - ⟪g' x, y - x⟫ - μ / 2 * ‖y - x‖ ^ 2) := by
  set r := y - x with hr
  set z := g' y - g' x - μ • r with hz
  set D := g y - g x - ⟪g' x, r⟫ - μ / 2 * ‖r‖ ^ 2 with hD
  set M := L - μ with hM
  have key : ∀ t : ℝ, t * ‖z‖ ^ 2 - M / 2 * t ^ 2 * ‖z‖ ^ 2 ≤ D := by
    intro t
    have h1 := hlow x (y - t • z)
    have h2 := hup y (y - t • z)
    have e1 : y - t • z - x = r - t • z := by simp only [hr]; abel
    have e2 : y - t • z - y = -(t • z) := by abel
    rw [e1] at h1
    rw [e2] at h2
    rw [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_neg_right,
      inner_smul_right] at h2
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      inner_sub_right, inner_smul_right] at h1
    have hzz : ⟪g' y, z⟫ - ⟪g' x, z⟫ - μ * ⟪r, z⟫ = ‖z‖ ^ 2 := by
      have : ‖z‖ ^ 2 = ⟪g' y - g' x - μ • r, z⟫ := by rw [← hz, real_inner_self_eq_norm_sq]
      rw [this]; simp only [inner_sub_left, real_inner_smul_left]
    have ht := congrArg (fun q => t * q) hzz
    rw [hD, hM]
    nlinarith
  have hD0 : 0 ≤ D := by simpa using key 0
  rcases lt_trichotomy M 0 with hneg | hzero | hpos
  · -- then r = 0
    have hup' : g y ≤ g x + ⟪g' x, r⟫ + L / 2 * ‖r‖ ^ 2 := hup x y
    have hDle : D ≤ M / 2 * ‖r‖ ^ 2 := by rw [hD, hM]; linarith
    have hr0 : ‖r‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖r‖]
    have hr0' : r = 0 := by
      have : ‖r‖ = 0 := by nlinarith [norm_nonneg r]
      exact norm_eq_zero.mp this
    have hyx : y = x := by rw [hr] at hr0'; exact sub_eq_zero.mp hr0'
    have hz0 : z = 0 := by simp [hz, hr0', hyx]
    have hD00 : D = 0 := by rw [hr0] at hDle; linarith
    rw [hz0, hD00]; simp
  · rw [hzero]
    by_contra hcon
    push_neg at hcon
    have hZ : 0 < ‖z‖ ^ 2 := by nlinarith
    have := key ((D + 1) / ‖z‖ ^ 2)
    rw [hzero] at this
    have e : (D + 1) / ‖z‖ ^ 2 * ‖z‖ ^ 2 = D + 1 := div_mul_cancel₀ _ hZ.ne'
    simp only [zero_div, zero_mul, sub_zero] at this
    linarith
  · have h := key (1 / M)
    have e : 1 / M * ‖z‖ ^ 2 - M / 2 * (1 / M) ^ 2 * ‖z‖ ^ 2 = ‖z‖ ^ 2 / (2 * M) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at h
    linarith

lemma lim_lemma (A B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * A + t ^ 2 * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  set t := min 1 (-A / (2 * (B + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -A / (2 * (B + 1)) := min_le_right _ _
  have := h t ht0 ht1
  have h3 : t * B ≤ -A / 2 := by
    have h4 : t * B ≤ (-A / (2 * (B + 1))) * B := mul_le_mul_of_nonneg_right ht2 hB
    have h5 : (-A / (2 * (B + 1))) * B ≤ -A / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  nlinarith

lemma prox_vi {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (γ : ℝ) (hγ : 0 < γ) (y p : EuclideanSpace ℝ (Fin d)) (hp : IsProxPoint h γ y p)
    (z : EuclideanSpace ℝ (Fin d)) :
    h p + 1 / γ * ⟪y - p, z - p⟫ ≤ h z := by
  set κ := 1 / (2 * γ) with hκ
  have hκ2 : 1 / γ = 2 * κ := by rw [hκ]; field_simp
  have hκ0 : 0 ≤ κ := by positivity
  rw [hκ2]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ t * (h z - h p - 2 * κ * ⟪y - p, z - p⟫) + t ^ 2 * (κ * ‖z - p‖ ^ 2) := by
    intro t ht0 ht1
    have h1 := hp (p + t • (z - p))
    have e : p + t • (z - p) = (1 - t) • p + t • z := by module
    have h2 := hh.2 (Set.mem_univ p) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring)
    rw [← e] at h2
    have e2 : p + t • (z - p) - y = (p - y) + t • (z - p) := by abel
    rw [e2, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right] at h1
    have e3 : ⟪y - p, z - p⟫ = -⟪p - y, z - p⟫ := by rw [← inner_neg_left, neg_sub]
    rw [e3]
    simp only [smul_eq_mul] at h2
    rw [← hκ] at h1
    nlinarith
  have := lim_lemma _ _ (by positivity) key
  linarith

lemma opt_vi {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (z : EuclideanSpace ℝ (Fin d)) :
    h xs - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, z - xs⟫ ≤ h z := by
  set v := z - xs with hv
  set G := (1 / (n : ℝ)) • ∑ i, f' i xs with hG
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ t * (h z - h xs + ⟪G, v⟫) + t ^ 2 * (L / 2 * ‖v‖ ^ 2) := by
    intro t ht0 ht1
    have h1 := hxs (xs + t • v)
    have e : xs + t • v = (1 - t) • xs + t • z := by rw [hv]; module
    have h2 := hh.2 (Set.mem_univ xs) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring)
    rw [← e] at h2
    simp only [smul_eq_mul] at h2
    have hsum : ∑ i, f i (xs + t • v) ≤
        ∑ i, (f i xs + t * ⟪f' i xs, v⟫ + L / 2 * t ^ 2 * ‖v‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have := sg_descent (f i) (f' i) (hgrad i) L (hlip i) xs (xs + t • v)
      rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
        sq_abs] at this
      linarith
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hGv : ⟪G, v⟫ = (1 / (n:ℝ)) * ∑ i, ⟪f' i xs, v⟫ := by
      rw [hG, inner_smul_left, sum_inner]; simp
    have h3 := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
    have e4 : 1 / (n:ℝ) * (∑ i, f i xs + t * ∑ i, ⟪f' i xs, v⟫ + n * (L / 2 * t ^ 2 * ‖v‖ ^ 2))
        = 1 / (n:ℝ) * ∑ i, f i xs + t * ((1 / (n:ℝ)) * ∑ i, ⟪f' i xs, v⟫)
          + L / 2 * t ^ 2 * ‖v‖ ^ 2 := by field_simp
    rw [e4, ← hGv] at h3
    nlinarith
  have := lim_lemma _ _ (by positivity) key
  rw [real_inner_comm] at this ⊢
  linarith

lemma prox_nonexp {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ : ℝ) (hγ : 0 < γ) (y p : EuclideanSpace ℝ (Fin d)) (hp : IsProxPoint h γ y p) :
    ‖p - xs‖ ^ 2 ≤ ‖y - (xs - γ • ((1 / (n : ℝ)) • ∑ i, f' i xs))‖ ^ 2 := by
  set G := (1 / (n : ℝ)) • ∑ i, f' i xs with hG
  have h1 := prox_vi h hh γ hγ y p hp xs
  have h2 := opt_vi hn f f' h L hL hgrad hlip hh xs hxs p
  rw [← hG] at h2
  set a := p - xs with ha
  set b := y - (xs - γ • G) with hb
  have e1 : y - p = b - a - γ • G := by rw [ha, hb]; abel
  have e2 : xs - p = -a := by rw [ha]; abel
  rw [e1, e2] at h1
  simp only [inner_neg_right, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real] at h1
  have h3 : 1 / γ * (-(⟪b, a⟫ - ‖a‖ ^ 2 - γ * ⟪G, a⟫)) ≤ ⟪G, a⟫ := by linarith
  have h4 : -(⟪b, a⟫ - ‖a‖ ^ 2 - γ * ⟪G, a⟫) ≤ γ * ⟪G, a⟫ := by
    have := mul_le_mul_of_nonneg_left h3 hγ.le
    rwa [← mul_assoc, mul_one_div_cancel hγ.ne', one_mul] at this
  have h5 := norm_sub_sq_real b a
  nlinarith [sq_nonneg ‖b - a‖]

lemma centered_sq {d n : ℕ} (hn : 0 < n) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∑ j, ‖a j - (1 / (n : ℝ)) • ∑ i, a i‖ ^ 2
      = ∑ j, ‖a j‖ ^ 2 - n * ‖(1 / (n : ℝ)) • ∑ i, a i‖ ^ 2 := by
  set m := (1 / (n : ℝ)) • ∑ i, a i with hm
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, a i = (n : ℝ) • m := by rw [hm, smul_smul]; field_simp; simp
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hs,
    inner_smul_left, real_inner_self_eq_norm_sq]
  simp
  ring

lemma centered_sum {d n : ℕ} (hn : 0 < n) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∑ j, (a j - (1 / (n : ℝ)) • ∑ i, a i) = 0 := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  field_simp
  simp

lemma young_pq {d : ℕ} (p q : EuclideanSpace ℝ (Fin d)) (β : ℝ) (hβ : 0 < β) :
    ‖p - q‖ ^ 2 ≤ (1 + β) * ‖p‖ ^ 2 + (1 + 1 / β) * ‖q‖ ^ 2 := by
  have h0 : 0 ≤ ‖β • p + q‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hβ, inner_smul_left] at h0
  simp only [RCLike.conj_to_real] at h0
  rw [norm_sub_sq_real]
  have e : (1 + β) * ‖p‖ ^ 2 + (1 + 1 / β) * ‖q‖ ^ 2 - (‖p‖ ^ 2 - 2 * ⟪p, q⟫ + ‖q‖ ^ 2)
      = ((β * ‖p‖) ^ 2 + 2 * (β * ⟪p, q⟫) + ‖q‖ ^ 2) / β := by
    field_simp; ring
  have : 0 ≤ ((β * ‖p‖) ^ 2 + 2 * (β * ⟪p, q⟫) + ‖q‖ ^ 2) / β := div_nonneg h0 hβ.le
  linarith

lemma avg_step {d n : ℕ} (hn : 0 < n) (u : EuclideanSpace ℝ (Fin d))
    (a b : Fin n → EuclideanSpace ℝ (Fin d)) (γ β : ℝ) (hβ : 0 < β) :
    (1 / (n : ℝ)) * ∑ j, ‖u - γ • (a j - b j + (1 / (n : ℝ)) • ∑ i, b i)‖ ^ 2 ≤
      ‖u‖ ^ 2 - 2 * γ * ⟪u, (1 / (n : ℝ)) • ∑ i, a i⟫
        + γ ^ 2 * ((1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖a j‖ ^ 2)
          - β * ‖(1 / (n : ℝ)) • ∑ i, a i‖ ^ 2
          + (1 + 1 / β) * ((1 / (n : ℝ)) * ∑ j, ‖b j‖ ^ 2)) := by
  set A := (1 / (n : ℝ)) • ∑ i, a i with hA
  set Bm := (1 / (n : ℝ)) • ∑ i, b i with hBm
  set w := u - γ • A with hw
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have pt : ∀ j, ‖u - γ • (a j - b j + Bm)‖ ^ 2 ≤
      ‖w‖ ^ 2 - 2 * γ * ⟪w, (a j - A) - (b j - Bm)⟫
        + γ ^ 2 * ((1 + β) * ‖a j - A‖ ^ 2 + (1 + 1 / β) * ‖b j - Bm‖ ^ 2) := by
    intro j
    have e : u - γ • (a j - b j + Bm) = w - γ • ((a j - A) - (b j - Bm)) := by
      rw [hw]; module
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have := young_pq (a j - A) (b j - Bm) β hβ
    have hg : 0 ≤ γ ^ 2 := sq_nonneg γ
    nlinarith [mul_le_mul_of_nonneg_left this hg]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => pt j)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← inner_sum,
    Finset.sum_sub_distrib, centered_sum hn a, centered_sum hn b, centered_sq hn a,
    centered_sq hn b] at hsum
  simp only [sub_zero, inner_zero_right, mul_zero, sub_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hw2 : ‖w‖ ^ 2 = ‖u‖ ^ 2 - 2 * γ * ⟪u, A⟫ + γ ^ 2 * ‖A‖ ^ 2 := by
    rw [hw, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have h3 := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
  have hB0 : 0 ≤ γ ^ 2 * (1 + 1 / β) * ‖Bm‖ ^ 2 := by positivity
  calc _ ≤ _ := h3
    _ = ‖w‖ ^ 2 + γ ^ 2 * ((1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖a j‖ ^ 2 - ‖A‖ ^ 2)
          + (1 + 1 / β) * ((1 / (n : ℝ)) * ∑ j, ‖b j‖ ^ 2 - ‖Bm‖ ^ 2)) := by
        rw [← hA, ← hBm]
        field_simp <;> ring
    _ ≤ _ := by rw [hw2]; nlinarith

lemma final_arith (N μ L γ c β D Fx U Qa Qb IP NA Y T : ℝ) (hN : 1 ≤ N) (hμ : 0 < μ)
    (hL : 0 < L) (hγ : γ = 1 / (2 * (μ * N + L))) (hc : c = 1 / (2 * γ * (1 - γ * μ) * N))
    (hβ : β = (2 * μ * N + L) / L)
    (hT : T ≤ (1 - 1 / N) * D + Fx / N + c * Y)
    (hY : Y ≤ U - 2 * γ * IP + γ ^ 2 * ((1 + β) * Qa - β * NA + (1 + 1 / β) * Qb))
    (hIP : 2 * (L - μ) * Fx + Qa + L * μ * U ≤ 2 * L * IP) (hPL : 2 * μ * Fx ≤ NA)
    (hB : Qb ≤ 2 * L * D) (hD : 0 ≤ D) :
    T ≤ (1 - γ * μ) * (D + c * U) := by
  have hN0 : (0:ℝ) < N := by linarith
  have hm : μ ≤ μ * N := by nlinarith
  have hs0 : 0 < μ * N + L := by nlinarith
  have hd0 : 0 < 2 * (μ * N + L) - μ := by nlinarith
  have hd1 : 0 < 2 * μ * N + L := by nlinarith
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  obtain ⟨q, hqdef⟩ : ∃ q, q = 2 * (μ * N + L) - μ := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; exact hd0
  have h1γμ : 1 - γ * μ = q / (2 * (μ * N + L)) := by
    rw [hqdef, hγ]; field_simp
  have hc' : c = 2 * (μ * N + L) ^ 2 / (q * N) := by
    rw [hc, h1γμ, hγ]; field_simp
  have hc0 : 0 < c := by rw [hc']; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have e1 := mul_le_mul_of_nonneg_left hIP (by positivity : (0:ℝ) ≤ γ / L)
  have e1' : γ / L * (2 * L * IP) = 2 * γ * IP := by field_simp
  have e2 := mul_le_mul_of_nonneg_left hPL hβ0.le
  have e3 := mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ) ≤ 1 + 1 / β)
  have br : (1 + β) * Qa - β * NA + (1 + 1 / β) * Qb ≤
      (1 + β) * Qa - β * (2 * μ * Fx) + (1 + 1 / β) * (2 * L * D) := by linarith
  have e4 := mul_le_mul_of_nonneg_left br (sq_nonneg γ)
  have hY2 : Y ≤ U - γ / L * (2 * (L - μ) * Fx + Qa + L * μ * U)
      + γ ^ 2 * ((1 + β) * Qa - β * (2 * μ * Fx) + (1 + 1 / β) * (2 * L * D)) := by
    rw [e1'] at e1
    linarith
  have hT2 := mul_le_mul_of_nonneg_left hY2 hc0.le
  set K := (1 - 1 / N) + c * γ ^ 2 * (1 + 1 / β) * (2 * L) - (1 - γ * μ) with hK
  have hid : (1 - 1 / N) * D + Fx / N + c * (U - γ / L * (2 * (L - μ) * Fx + Qa + L * μ * U)
      + γ ^ 2 * ((1 + β) * Qa - β * (2 * μ * Fx) + (1 + 1 / β) * (2 * L * D)))
      = (1 - γ * μ) * (D + c * U) + K * D := by
    rw [hK, h1γμ, hc', hβ, hγ]
    field_simp
    rw [hqdef]
    ring
  have hKle : K ≤ 0 := by
    have hpoly : 0 ≤ (2 * (μ * N + L) - μ) * (2 * μ * N + L) * (μ * N + 2 * L)
        - 4 * L * (μ * N + L) ^ 2 := by
      have e : (2 * (μ * N + L) - μ) * (2 * μ * N + L) * (μ * N + 2 * L)
          - 4 * L * (μ * N + L) ^ 2 = (μ * N) * (2 * (μ * N) ^ 2 + 5 * (μ * N) * L + 4 * L ^ 2)
            + (μ * N - μ) * ((2 * μ * N + L) * (μ * N + 2 * L)) := by ring
      rw [e]
      have : 0 ≤ μ * N - μ := by linarith
      positivity
    have hKe : K = -(((2 * (μ * N + L) - μ) * (2 * μ * N + L) * (μ * N + 2 * L)
        - 4 * L * (μ * N + L) ^ 2)
        / (2 * (μ * N + L) * N * q * (2 * μ * N + L))) := by
      rw [hK, h1γμ, hc', hβ, hγ, ← hqdef]
      field_simp
      rw [hqdef]
      ring
    rw [hKe, neg_nonpos]
    apply div_nonneg hpoly
    positivity
  have := mul_nonpos_of_nonpos_of_nonneg hKle hD
  linarith

noncomputable def bregF {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (i : Fin n) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  f i y - f i xs - ⟪f' i xs, y - xs⟫

lemma lyap_eq {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (xs : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    lyapunov f f' c xs s = (1 / (n : ℝ)) * ∑ i, bregF f f' xs i (s.2 i) + c * ‖s.1 - xs‖ ^ 2 := by
  unfold lyapunov bregF
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring

lemma update_sum {d n : ℕ} (F : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (φ : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, F i (Function.update φ j x i) = ∑ i, F i (φ i) + (F j x - F j (φ j)) := by
  have : ∀ i, F i (Function.update φ j x i) =
      F i (φ i) + if i = j then F j x - F j (φ j) else 0 := by
    intro i; by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

set_option maxHeartbeats 1000000 in
theorem theorem1_core {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ c : ℝ) (hγ : γ = 1 / (2 * (μ * n + L))) (hc : c = 1 / (2 * γ * (1 - γ * μ) * n))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x : EuclideanSpace ℝ (Fin d)) (φ : Fin n → EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' c xs (sagaStep f' P γ (x, φ) j) ≤
      (1 - γ * μ) * lyapunov f f' c xs (x, φ) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hm : μ ≤ μ * n := by nlinarith
  have hγμ : 0 < 1 - γ * μ := by
    rw [hγ, sub_pos, one_div_mul_eq_div, div_lt_one (by positivity)]; nlinarith
  have hc0 : 0 < c := by rw [hc]; positivity
  set β : ℝ := (2 * μ * n + L) / L with hβ
  have hβ0 : 0 < β := by positivity
  set u := x - xs with hu
  set G := (1 / (n : ℝ)) • ∑ i, f' i xs with hG
  set Bm := (1 / (n : ℝ)) • ∑ i, (f' i (φ i) - f' i xs) with hBm
  set Fb := bregF f f' xs with hFb
  -- per-step bound
  have hstep : ∀ j, lyapunov f f' c xs (sagaStep f' P γ (x, φ) j) ≤
      (1 / (n : ℝ)) * (∑ i, Fb i (φ i) + (Fb j x - Fb j (φ j)))
        + c * ‖u - γ • ((f' j x - f' j xs) - (f' j (φ j) - f' j xs) + Bm)‖ ^ 2 := by
    intro j
    rw [lyap_eq]
    simp only [sagaStep]
    rw [update_sum]
    have hne := prox_nonexp hn f f' h L hL hgrad hlip hh xs hxs γ hγ0 _ _ (hP (sagaW f' γ x φ j))
    have ew : sagaW f' γ x φ j - (xs - γ • ((1 / (n : ℝ)) • ∑ i, f' i xs)) =
        u - γ • ((f' j x - f' j xs) - (f' j (φ j) - f' j xs) + Bm) := by
      rw [hu, hBm, Finset.sum_sub_distrib]
      unfold sagaW
      module
    rw [ew] at hne
    have := mul_le_mul_of_nonneg_left hne hc0.le
    linarith
  -- averaged
  set S := ∑ i, Fb i (φ i) with hS
  set SX := ∑ j, Fb j x with hSX
  set Y' := ∑ j, ‖u - γ • ((f' j x - f' j xs) - (f' j (φ j) - f' j xs) + Bm)‖ ^ 2 with hY'
  have hT : (1 / (n : ℝ)) * ∑ j, lyapunov f f' c xs (sagaStep f' P γ (x, φ) j) ≤
      (1 - 1 / (n:ℝ)) * ((1 / (n:ℝ)) * S) + ((1 / (n:ℝ)) * SX) / n + c * ((1 / (n:ℝ)) * Y') := by
    calc _ ≤ (1 / (n : ℝ)) * ∑ j, ((1 / (n : ℝ)) * (S + (Fb j x - Fb j (φ j)))
          + c * ‖u - γ • ((f' j x - f' j xs) - (f' j (φ j) - f' j xs) + Bm)‖ ^ 2) := by
          gcongr with j; exact hstep j
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
            Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← hS, ← hSX, ← hY']
          field_simp
          ring
  have hY := avg_step hn u (fun j => f' j x - f' j xs) (fun j => f' j (φ j) - f' j xs) γ β hβ0
  beta_reduce at hY
  rw [← hBm, ← hY'] at hY
  set A := (1 / (n : ℝ)) • ∑ i, (f' i x - f' i xs) with hA
  -- per-component facts
  have hlow0 : ∀ i (a w : EuclideanSpace ℝ (Fin d)),
      f i a + ⟪f' i a, w - a⟫ + 0 / 2 * ‖w - a‖ ^ 2 ≤ f i w := by
    intro i a w
    have := sg_strong_lower (f i) μ (f' i a) a w (hsc i) (hgrad i a)
    have : 0 ≤ μ / 2 * ‖w - a‖ ^ 2 := by positivity
    simp only [zero_div, zero_mul, add_zero]; linarith
  have hFb0 : ∀ i y, 0 ≤ Fb i y := by
    intro i y
    have := hlow0 i xs y
    simp only [hFb, bregF]; simp only [zero_div, zero_mul, add_zero] at this; linarith
  have hBi : ∀ i y, ‖f' i y - f' i xs‖ ^ 2 ≤ 2 * L * Fb i y := by
    intro i y
    have := sg_cocoer (f i) (f' i) 0 L (hlow0 i)
      (fun a b => sg_descent (f i) (f' i) (hgrad i) L (hlip i) a b) xs y
    simp only [zero_smul, sub_zero, zero_div, zero_mul] at this
    simp only [hFb, bregF]; linarith
  have hper : ∀ i, 2 * (L - μ) * Fb i x + ‖f' i x - f' i xs‖ ^ 2 + L * μ * ‖u‖ ^ 2 ≤
      2 * L * ⟪f' i x - f' i xs, u⟫ := by
    intro i
    have hc1 := sg_cocoer (f i) (f' i) μ L
      (fun a b => sg_strong_lower (f i) μ (f' i a) a b (hsc i) (hgrad i a))
      (fun a b => sg_descent (f i) (f' i) (hgrad i) L (hlip i) a b) x xs
    have e : f' i xs - f' i x - μ • (xs - x) = -((f' i x - f' i xs) - μ • u) := by
      rw [hu]; module
    have e2 : xs - x = -u := by rw [hu]; abel
    rw [e, norm_neg, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right, e2, inner_neg_right, norm_neg] at hc1
    have e3 : ⟪f' i x, u⟫ = ⟪f' i x - f' i xs, u⟫ + ⟪f' i xs, u⟫ := by
      rw [inner_sub_left]; ring
    simp only [hFb, bregF]
    rw [← hu]
    nlinarith
  have hlowi : ∀ i, Fb i x + μ / 2 * ‖u‖ ^ 2 ≤ ⟪f' i x - f' i xs, u⟫ := by
    intro i
    have := sg_strong_lower (f i) μ (f' i x) x xs (hsc i) (hgrad i x)
    have e2 : xs - x = -u := by rw [hu]; abel
    rw [e2, inner_neg_right, norm_neg] at this
    rw [inner_sub_left]
    simp only [hFb, bregF]
    rw [← hu]
    linarith
  -- averaged facts
  have hIPeq : ⟪u, A⟫ = (1 / (n:ℝ)) * ∑ i, ⟪f' i x - f' i xs, u⟫ := by
    rw [hA, inner_smul_right, inner_sum]
    simp_rw [real_inner_comm u]
  have hsumper := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← hSX] at hsumper
  have hIP : 2 * (L - μ) * ((1 / (n:ℝ)) * SX) + (1 / (n:ℝ)) * ∑ j, ‖f' j x - f' j xs‖ ^ 2
      + L * μ * ‖u‖ ^ 2 ≤ 2 * L * ⟪u, A⟫ := by
    rw [hIPeq]
    have := mul_le_mul_of_nonneg_left hsumper (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
    have e : 1 / (n:ℝ) * (L * μ * (n * ‖u‖ ^ 2)) = L * μ * ‖u‖ ^ 2 := by field_simp
    nlinarith
  have hsumlow := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlowi i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hSX] at hsumlow
  have hlowavg : (1 / (n:ℝ)) * SX + μ / 2 * ‖u‖ ^ 2 ≤ ⟪u, A⟫ := by
    rw [hIPeq]
    have := mul_le_mul_of_nonneg_left hsumlow (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
    have e : 1 / (n:ℝ) * (n * (μ / 2 * ‖u‖ ^ 2)) = μ / 2 * ‖u‖ ^ 2 := by field_simp
    nlinarith
  have hPL : 2 * μ * ((1 / (n:ℝ)) * SX) ≤ ‖A‖ ^ 2 := by
    have h0 : 0 ≤ ‖A - μ • u‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, norm_smul μ u, Real.norm_eq_abs, abs_of_pos hμ, inner_smul_right,
      real_inner_comm] at h0
    have h2 := mul_le_mul_of_nonneg_left hlowavg (by positivity : (0:ℝ) ≤ 2 * μ)
    rw [mul_pow] at h0
    linarith
  have hBsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hBi i (φ i))
  rw [← Finset.mul_sum, ← hS] at hBsum
  have hB : (1 / (n:ℝ)) * ∑ j, ‖f' j (φ j) - f' j xs‖ ^ 2 ≤ 2 * L * ((1 / (n:ℝ)) * S) := by
    have := mul_le_mul_of_nonneg_left hBsum (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
    linarith
  have hD : 0 ≤ (1 / (n:ℝ)) * S := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => hFb0 i (φ i))
  have hfin := final_arith (n:ℝ) μ L γ c β ((1 / (n:ℝ)) * S) ((1 / (n:ℝ)) * SX) (‖u‖ ^ 2)
    ((1 / (n:ℝ)) * ∑ j, ‖f' j x - f' j xs‖ ^ 2) ((1 / (n:ℝ)) * ∑ j, ‖f' j (φ j) - f' j xs‖ ^ 2)
    ⟪u, A⟫ (‖A‖ ^ 2) ((1 / (n:ℝ)) * Y') _ hN1 hμ hL hγ hc hβ hT hY hIP hPL hB hD
  rw [lyap_eq]
  simpa [hS, hu] using hfin

lemma sum_snoc_split {n k : ℕ} (g : (Fin (k + 1) → Fin n) → ℝ) :
    ∑ js, g js = ∑ js' : Fin k → Fin n, ∑ j : Fin n, g (Fin.snoc js' j) := by
  rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma run_snoc {d n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (js' : Fin k → Fin n) (j : Fin n) :
    sagaRun f' P γ x0 (k + 1) (Fin.snoc js' j) = sagaStep f' P γ (sagaRun f' P γ x0 k js') j := by
  simp only [sagaRun, Fin.snoc_castSucc, Fin.snoc_last]

theorem corollary_core {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2 ≤
      (1 - μ / (2 * (μ * n + L))) ^ k *
        (‖x0 - xs‖ ^ 2 + n / (μ * n + L) *
          ((1 / (n : ℝ)) * ∑ i, f i x0 - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x0 - xs⟫_ℝ
            - (1 / (n : ℝ)) * ∑ i, f i xs)) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hN1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < μ * n + L := by nlinarith
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hγμe : γ * μ = μ / (2 * (μ * n + L)) := by rw [hγ]; ring
  have hγμ : 0 < 1 - γ * μ := by
    rw [hγμe, sub_pos, div_lt_one (by positivity)]; nlinarith
  set c := 1 / (2 * γ * (1 - γ * μ) * n) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set ρ := 1 - γ * μ with hρ
  set T := lyapunov f f' c xs with hT
  have hFb0 : ∀ i y, 0 ≤ bregF f f' xs i y := by
    intro i y
    have := sg_strong_lower (f i) μ (f' i xs) xs y (hsc i) (hgrad i xs)
    have : 0 ≤ μ / 2 * ‖y - xs‖ ^ 2 := by positivity
    unfold bregF; linarith
  have hE : ∀ k : ℕ, (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, T (sagaRun f' P γ x0 k js) ≤
      ρ ^ k * T (x0, fun _ => x0) := by
    intro k
    induction k with
    | zero => simp [sagaRun]
    | succ k ih =>
      rw [sum_snoc_split]
      simp_rw [run_snoc]
      have hstep : ∀ js' : Fin k → Fin n,
          (1 / (n : ℝ)) * ∑ j, T (sagaStep f' P γ (sagaRun f' P γ x0 k js') j) ≤
            ρ * T (sagaRun f' P γ x0 k js') := by
        intro js'
        have := theorem1_core hn f f' h μ L hμ hL hgrad hsc hlip hh xs hxs γ c hγ hc P hP
          (sagaRun f' P γ x0 k js').1 (sagaRun f' P γ x0 k js').2
        simpa using this
      calc (1 / (n : ℝ) ^ (k + 1)) * ∑ js' : Fin k → Fin n,
            ∑ j, T (sagaStep f' P γ (sagaRun f' P γ x0 k js') j)
          = (1 / (n : ℝ) ^ k) * ∑ js' : Fin k → Fin n,
            ((1 / (n : ℝ)) * ∑ j, T (sagaStep f' P γ (sagaRun f' P γ x0 k js') j)) := by
            rw [← Finset.mul_sum, pow_succ]; field_simp
        _ ≤ (1 / (n : ℝ) ^ k) * ∑ js' : Fin k → Fin n, ρ * T (sagaRun f' P γ x0 k js') := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum (fun js' _ => hstep js')
        _ = ρ * ((1 / (n : ℝ) ^ k) * ∑ js' : Fin k → Fin n, T (sagaRun f' P γ x0 k js')) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ ρ * (ρ ^ k * T (x0, fun _ => x0)) := by gcongr
        _ = ρ ^ (k + 1) * T (x0, fun _ => x0) := by ring
  have hTge : ∀ s, c * ‖s.1 - xs‖ ^ 2 ≤ T s := by
    intro s
    rw [hT, lyap_eq]
    have : 0 ≤ (1 / (n : ℝ)) * ∑ i, bregF f f' xs i (s.2 i) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hFb0 i _))
    linarith
  have hsum : c * ((1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2)
      ≤ (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, T (sagaRun f' P γ x0 k js) := by
    rw [← mul_assoc, mul_comm c, mul_assoc, Finset.mul_sum]
    gcongr with js
    exact hTge _
  have hT0 : T (x0, fun _ => x0) = (1 / (n : ℝ)) * ∑ i, bregF f f' xs i x0 + c * ‖x0 - xs‖ ^ 2 := by
    rw [hT, lyap_eq]
  have hW : (1 / (n : ℝ)) * ∑ i, f i x0 - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x0 - xs⟫_ℝ
      - (1 / (n : ℝ)) * ∑ i, f i xs = (1 / (n : ℝ)) * ∑ i, bregF f f' xs i x0 := by
    unfold bregF
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, inner_smul_left, sum_inner]
    simp only [RCLike.conj_to_real]
    ring
  rw [hW, ← hγμe]
  set W := (1 / (n : ℝ)) * ∑ i, bregF f f' xs i x0 with hWdef
  have hW0 : 0 ≤ W := mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hFb0 i _))
  set E := (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2
  have h1 : c * E ≤ ρ ^ k * (W + c * ‖x0 - xs‖ ^ 2) := by
    have := hE k
    rw [hT0] at this
    linarith
  have hcinv : W ≤ c * (n / (μ * n + L) * W) := by
    have e : c * (n / (μ * n + L)) = 1 / ρ := by
      rw [hc, hρ, hγ]; field_simp
    have hρ1 : ρ ≤ 1 := by rw [hρ]; nlinarith
    have : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hγμ]; linarith
    rw [← mul_assoc, e]
    nlinarith
  have hρk : 0 ≤ ρ ^ k := pow_nonneg hγμ.le k
  have h2 : c * E ≤ c * (ρ ^ k * (‖x0 - xs‖ ^ 2 + n / (μ * n + L) * W)) := by
    have := mul_le_mul_of_nonneg_left hcinv hρk
    nlinarith
  exact le_of_mul_le_mul_left h2 hc0

end SAGA.StronglyConvex

open SAGA.StronglyConvex


theorem solution {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (h : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d))
    (hxs : ∀ y, (1 / (n : ℝ)) * ∑ i, f i xs + h xs ≤ (1 / (n : ℝ)) * ∑ i, f i y + h y)
    (γ : ℝ) (hγ : γ = 1 / (2 * (μ * n + L)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h γ y (P y))
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    (1 / (n : ℝ) ^ k) * ∑ js : Fin k → Fin n, ‖(sagaRun f' P γ x0 k js).1 - xs‖ ^ 2 ≤
      (1 - μ / (2 * (μ * n + L))) ^ k *
        (‖x0 - xs‖ ^ 2 + n / (μ * n + L) *
          ((1 / (n : ℝ)) * ∑ i, f i x0 - ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x0 - xs⟫_ℝ
            - (1 / (n : ℝ)) * ∑ i, f i xs)) := by
  exact corollary_core hn f f' h μ L hμ hL hgrad hsc hlip hh xs hxs γ hγ P hP x0 k
