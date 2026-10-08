-- Prove2me | solution 1 for SAGA.StronglyConvex.lemma1_inner_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:45:19.006112+00:00
-- url     : https://prove2.me/submissions/e051eba3-37ee-4c61-ace0-4b2a2d5fb0ca

import Mathlib

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

theorem lemma1_core {d n : ℕ} (hn : 0 < n) {L μ : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, StrongConvexOn Set.univ μ (f i))
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪(1 / (n : ℝ)) • ∑ i, f' i x, xs - x⟫_ℝ ≤
      (L - μ) / L * ((1 / (n : ℝ)) * ∑ i, f i xs - (1 / (n : ℝ)) * ∑ i, f i x) - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x - xs⟫_ℝ := by
  set r := xs - x with hr
  have per : ∀ i, ⟪f' i x, r⟫ ≤ (L - μ) / L * (f i xs - f i x) - μ / 2 * ‖r‖ ^ 2
      - 1 / (2 * L) * ‖f' i xs - f' i x‖ ^ 2 + μ / L * ⟪f' i xs, r⟫ := by
    intro i
    have hc := sg_cocoer (f i) (f' i) μ L
      (fun a b => sg_strong_lower (f i) μ (f' i a) a b (hconv i) (hgrad i a))
      (fun a b => sg_descent (f i) (f' i) (hgrad i) L (hLip i) a b) x xs
    rw [← hr] at hc
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      inner_sub_left] at hc
    have key2 : 0 ≤ (2 * (L - μ) * (f i xs - f i x) - L * μ * ‖r‖ ^ 2 - ‖f' i xs - f' i x‖ ^ 2
          + 2 * μ * ⟪f' i xs, r⟫ - 2 * L * ⟪f' i x, r⟫) / (2 * L) :=
      div_nonneg (by nlinarith) (by positivity)
    have e : (2 * (L - μ) * (f i xs - f i x) - L * μ * ‖r‖ ^ 2 - ‖f' i xs - f' i x‖ ^ 2
          + 2 * μ * ⟪f' i xs, r⟫ - 2 * L * ⟪f' i x, r⟫) / (2 * L) =
        ((L - μ) / L * (f i xs - f i x) - μ / 2 * ‖r‖ ^ 2
          - 1 / (2 * L) * ‖f' i xs - f' i x‖ ^ 2 + μ / L * ⟪f' i xs, r⟫) - ⟪f' i x, r⟫ := by
      field_simp
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => per i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  rw [inner_smul_left, inner_smul_left, sum_inner, sum_inner]
  have e2 : x - xs = -r := by simp [hr]
  rw [e2]
  simp only [inner_neg_right, Finset.sum_neg_distrib, RCLike.conj_to_real]
  rw [← Finset.sum_sub_distrib] at hsum
  have e3 : ∑ i, f i xs - ∑ i, f i x = ∑ i, (f i xs - f i x) := by
    rw [Finset.sum_sub_distrib]
  set S1 := ∑ i, ⟪f' i x, r⟫
  set S2 := ∑ i, (f i xs - f i x)
  set S3 := ∑ i, ‖f' i xs - f' i x‖ ^ 2
  set S4 := ∑ i, ⟪f' i xs, r⟫
  rw [← mul_sub, e3]
  have e4 : 1 / (n:ℝ) * S1 ≤ 1 / n * ((L - μ) / L * S2 - μ / 2 * (n * ‖r‖ ^ 2) -
      1 / (2 * L) * S3 + μ / L * S4) := mul_le_mul_of_nonneg_left hsum (by positivity)
  have e5 : 1 / (n:ℝ) * ((L - μ) / L * S2 - μ / 2 * (n * ‖r‖ ^ 2) -
      1 / (2 * L) * S3 + μ / L * S4) = (L - μ) / L * (1 / ↑n * S2) - μ / 2 * ‖r‖ ^ 2 -
      1 / (2 * L * ↑n) * S3 - μ / L * (1 / ↑n * -S4) := by
    field_simp; ring
  linarith

end SAGA.StronglyConvex

open SAGA.StronglyConvex


theorem solution {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (μ L : ℝ) (hμ : 0 < μ) (hL : 0 < L)
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hsc : ∀ i, StrongConvexOn Set.univ μ (f i))
    (hlip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (x xs : EuclideanSpace ℝ (Fin d)) :
    ⟪(1 / (n : ℝ)) • ∑ i, f' i x, xs - x⟫_ℝ ≤
      (L - μ) / L * ((1 / (n : ℝ)) * ∑ i, f i xs - (1 / (n : ℝ)) * ∑ i, f i x)
        - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪(1 / (n : ℝ)) • ∑ i, f' i xs, x - xs⟫_ℝ := by
  exact lemma1_core hn hL hμ.le f f' hgrad hlip hsc x xs
