-- Prove2me | solution 1 for SAGA.Convex.lyapunov_one_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:52:31.24537+00:00
-- url     : https://prove2.me/submissions/5f8f082f-8e82-4566-853a-1bb82574a2b4

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_lyapunov

open scoped RealInnerProductSpace

namespace SAGA.Convex

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
    ⟪gradAvg f' x, xs - x⟫ ≤
      (L - μ) / L * (fAvg f xs - fAvg f x) - μ / 2 * ‖xs - x‖ ^ 2
        - 1 / (2 * L * n) * ∑ i, ‖f' i xs - f' i x‖ ^ 2
        - μ / L * ⟪gradAvg f' xs, x - xs⟫ := by
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
  unfold gradAvg fAvg
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


lemma sg_limit (A B K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * K) :
    A ≤ B := by
  by_contra hcon
  push_neg at hcon
  set t := min 1 ((A - B) / (K + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
  have h0 := h t ht0 (min_le_left _ _)
  have h1 : t * K ≤ (A - B) / (K + 1) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK
  have h2 : (A - B) / (K + 1) * K < A - B := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- variational inequality of a prox point -/
lemma sg_prox_vi {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    {γ : ℝ} (hγ : 0 < γ) (y p : EuclideanSpace ℝ (Fin d)) (hp : IsProxPoint h γ y p)
    (z : EuclideanSpace ℝ (Fin d)) :
    h p + 1 / γ * ⟪y - p, z - p⟫ ≤ h z := by
  set a := p - y with ha
  set dd := z - p with hd
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      h p ≤ h z - 1 / γ * ⟪y - p, dd⟫ + t * (1 / (2 * γ) * ‖dd‖ ^ 2) := by
    intro t ht0 ht1
    have hconv : h ((1 - t) • p + t • z) ≤ (1 - t) • h p + t • h z :=
      hh.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) ht0.le (by ring)
    have hopt := hp ((1 - t) • p + t • z)
    have hrw : (1 - t) • p + t • z - y = a + t • dd := by
      simp only [ha, hd]; module
    rw [hrw] at hopt
    have hexp : ‖a + t • dd‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * ⟪a, dd⟫ + t ^ 2 * ‖dd‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [hexp] at hopt
    simp only [smul_eq_mul] at hconv
    have hya : y - p = -a := by simp [ha]
    rw [hya, inner_neg_left]
    have hc : 0 < 1 / (2 * γ) := by positivity
    have e1 : 1 / γ = 2 * (1 / (2 * γ)) := by field_simp
    rw [e1]
    set c := 1 / (2 * γ)
    have h2 : t * h p ≤ t * (h z + 2 * c * ⟪a, dd⟫ + t * (c * ‖dd‖ ^ 2)) := by nlinarith
    have := le_of_mul_le_mul_left h2 ht0
    linarith
  have := sg_limit (h p) (h z - 1 / γ * ⟪y - p, dd⟫) (1 / (2 * γ) * ‖dd‖ ^ 2) (by positivity) key
  linarith

/-- firm nonexpansiveness from two variational inequalities -/
lemma sg_firm {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (y1 y2 p1 p2 : EuclideanSpace ℝ (Fin d))
    (h1 : ∀ z, h p1 + 1 / γ * ⟪y1 - p1, z - p1⟫ ≤ h z)
    (h2 : ∀ z, h p2 + 1 / γ * ⟪y2 - p2, z - p2⟫ ≤ h z) :
    ‖p1 - p2‖ ^ 2 ≤ ⟪y1 - y2, p1 - p2⟫ := by
  have e1 := h1 p2
  have e2 := h2 p1
  have hid : ⟪y1 - p1, p2 - p1⟫ + ⟪y2 - p2, p1 - p2⟫ = ‖p1 - p2‖ ^ 2 - ⟪y1 - y2, p1 - p2⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have : p2 - p1 = -(p1 - p2) := by abel
    rw [this, inner_neg_right]
    simp only [inner_sub_left]
    ring
  have hs : 1 / γ * (⟪y1 - p1, p2 - p1⟫ + ⟪y2 - p2, p1 - p2⟫) ≤ 0 := by linarith
  rw [hid] at hs
  have := (mul_nonpos_iff.mp hs)
  rcases this with ⟨_, h4⟩ | ⟨h3, _⟩
  · linarith
  · have : 0 < 1 / γ := by positivity
    linarith

lemma sg_firm2 {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) (hab : ‖b‖ ^ 2 ≤ ⟪a, b⟫) :
    ⟪a, b⟫ ≤ ‖a‖ ^ 2 := by
  have := norm_sub_sq_real a b
  nlinarith [sq_nonneg ‖a - b‖]

lemma sg_avg_lower {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hi : ∀ i, f i x + ⟪f' i x, y - x⟫ + c ≤ f i y) :
    fAvg f x + ⟪gradAvg f' x, y - x⟫ + c ≤ fAvg f y := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  unfold fAvg gradAvg
  rw [inner_smul_left, sum_inner, RCLike.conj_to_real]
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / n)
  have e : 1 / (n:ℝ) * (n * c) = c := by field_simp
  nlinarith

lemma sg_avg_upper {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hi : ∀ i, f i y ≤ f i x + ⟪f' i x, y - x⟫ + c) :
    fAvg f y ≤ fAvg f x + ⟪gradAvg f' x, y - x⟫ + c := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  unfold fAvg gradAvg
  rw [inner_smul_left, sum_inner, RCLike.conj_to_real]
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / n)
  have e : 1 / (n:ℝ) * (n * c) = c := by field_simp
  nlinarith

/-- first-order optimality of xs as a VI for the prox map at xs - γ ∇f(xs) -/
lemma sg_opt_vi {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    {γ : ℝ} (hγ : 0 < γ) (z : EuclideanSpace ℝ (Fin d)) :
    h xs + 1 / γ * ⟪(xs - γ • gradAvg f' xs) - xs, z - xs⟫ ≤ h z := by
  have e : (xs - γ • gradAvg f' xs) - xs = -(γ • gradAvg f' xs) := by abel
  rw [e, inner_neg_left, inner_smul_left, RCLike.conj_to_real]
  have e2 : 1 / γ * -(γ * ⟪gradAvg f' xs, z - xs⟫) = -⟪gradAvg f' xs, z - xs⟫ := by
    field_simp
  rw [e2]
  set dd := z - xs with hd
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      h xs ≤ (h z + ⟪gradAvg f' xs, dd⟫) + t * (L / 2 * ‖dd‖ ^ 2) := by
    intro t ht0 ht1
    have hconv : h ((1 - t) • xs + t • z) ≤ (1 - t) • h xs + t • h z :=
      hh.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) ht0.le (by ring)
    have ho := hopt ((1 - t) • xs + t • z)
    have hup := sg_avg_upper hn f f' xs ((1 - t) • xs + t • z) (L / 2 * ‖(1 - t) • xs + t • z - xs‖ ^ 2)
      (fun i => sg_descent (f i) (f' i) (hgrad i) L (hLip i) xs _)
    have hrw : (1 - t) • xs + t • z - xs = t • dd := by simp only [hd]; module
    rw [hrw, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs] at hup
    simp only [smul_eq_mul] at hconv
    have h2 : t * h xs ≤ t * ((h z + ⟪gradAvg f' xs, dd⟫) + t * (L / 2 * ‖dd‖ ^ 2)) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 ht0
  have := sg_limit _ _ _ (by positivity) key
  linarith

lemma sg_delta_eq {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {γ : ℝ} (hγ : γ ≠ 0)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    sagaW f' γ s j = s.1 - γ • (gradAvg f' s.1 + sagaDelta f' γ s j) := by
  unfold sagaDelta
  rw [smul_add, smul_sub, smul_smul, show γ * -(1 / γ) = -1 by field_simp, neg_one_smul]
  abel

lemma sg_delta_v {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {γ : ℝ} (hγ : γ ≠ 0)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    sagaDelta f' γ s j = (f' j s.1 - f' j (s.2 j) + (1 / (n : ℝ)) • ∑ i, f' i (s.2 i))
      - gradAvg f' s.1 := by
  unfold sagaDelta sagaW
  congr 1
  rw [sub_sub_cancel_left, smul_neg, smul_smul, show -(1 / γ) * γ = -1 by field_simp,
    neg_one_smul, neg_neg]

lemma sg_delta_sum {d n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) {γ : ℝ} (hγ : γ ≠ 0)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    ∑ j, sagaDelta f' γ s j = 0 := by
  simp only [sg_delta_v f' hγ s, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, gradAvg]
  have hN : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul,
    mul_one_div_cancel hN, one_smul, one_smul]
  abel

/-- one prox-gradient step inequality (Xiao–Zhang) -/
lemma sg_xz {d : ℕ} (fa h : EuclideanSpace ℝ (Fin d) → ℝ) (G Δ x xs w xp : EuclideanSpace ℝ (Fin d))
    {γ L : ℝ} (hγ : 0 < γ) (hγL : γ * L ≤ 1) (hL : 0 ≤ L)
    (hw : w = x - γ • (G + Δ))
    (hlow : fa x + ⟪G, xs - x⟫ ≤ fa xs)
    (hup : fa xp ≤ fa x + ⟪G, xp - x⟫ + L / 2 * ‖xp - x‖ ^ 2)
    (hvi : h xp + 1 / γ * ⟪w - xp, xs - xp⟫ ≤ h xs) :
    ‖xp - xs‖ ^ 2 ≤ ‖x - xs‖ ^ 2 - 2 * γ * ((fa xp + h xp) - (fa xs + h xs))
      - 2 * γ * ⟪Δ, xp - xs⟫ := by
  obtain ⟨a, rfl⟩ : ∃ a, xs = x - a := ⟨x - xs, by abel⟩
  obtain ⟨b, rfl⟩ : ∃ b, xp = x + b := ⟨xp - x, by abel⟩
  subst hw
  have e1 : x + b - (x - a) = a + b := by abel
  have e2 : x - a - x = -a := by abel
  have e3 : x + b - x = b := by abel
  have e4 : x - γ • (G + Δ) - (x + b) = -(γ • (G + Δ)) - b := by abel
  have e5 : x - a - (x + b) = -(a + b) := by abel
  have e6 : x - (x - a) = a := by abel
  rw [e1, e6]
  rw [e2] at hlow
  rw [e3] at hup
  rw [e4, e5] at hvi
  have hv : γ * (1 / γ * ⟪-(γ • (G + Δ)) - b, -(a + b)⟫) =
      γ * ⟪G, a⟫ + γ * ⟪G, b⟫ + γ * ⟪Δ, a⟫ + γ * ⟪Δ, b⟫ + ⟪b, a⟫ + ‖b‖ ^ 2 := by
    rw [← mul_assoc, mul_one_div_cancel hγ.ne', one_mul]
    simp only [inner_neg_right, inner_neg_left, inner_sub_left, inner_add_right, inner_add_left,
      inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
    ring
  have hvi' := mul_le_mul_of_nonneg_left hvi hγ.le
  rw [mul_add, hv] at hvi'
  rw [inner_neg_right] at hlow
  have hlow' := mul_le_mul_of_nonneg_left hlow hγ.le
  have hup' := mul_le_mul_of_nonneg_left hup hγ.le
  have hb := mul_le_mul_of_nonneg_right hγL (by positivity : (0:ℝ) ≤ ‖b‖ ^ 2)
  rw [norm_add_sq_real, inner_add_right]
  have hc := real_inner_comm a b
  nlinarith


/-- per-index bound used by the prox-SVRG inequality -/
lemma sg_svrg_j {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    ‖(sagaStep f' P (1 / (3 * L)) s j).1 - xs‖ ^ 2 ≤ ‖s.1 - xs‖ ^ 2
      - 2 * (1 / (3 * L)) * ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1
          + h (sagaStep f' P (1 / (3 * L)) s j).1) - (fAvg f xs + h xs))
      - 2 * (1 / (3 * L)) * ⟪sagaDelta f' (1 / (3 * L)) s j,
          P (s.1 - (1 / (3 * L)) • gradAvg f' s.1) - xs⟫
      + 2 * (1 / (3 * L)) ^ 2 * ‖sagaDelta f' (1 / (3 * L)) s j‖ ^ 2 := by
  set γ := 1 / (3 * L) with hγdef
  have hγ : 0 < γ := by positivity
  have hγL : γ * L ≤ 1 := by rw [hγdef]; field_simp; norm_num
  set G := gradAvg f' s.1
  set Δ := sagaDelta f' γ s j
  set w := sagaW f' γ s j
  set xb := P (s.1 - γ • G)
  have hxp : (sagaStep f' P γ s j).1 = P w := rfl
  rw [hxp]
  have hw : w = s.1 - γ • (G + Δ) := sg_delta_eq f' hγ.ne' s j
  have hvi := sg_prox_vi h hh hγ w (P w) (hP w)
  have hvib := sg_prox_vi h hh hγ (s.1 - γ • G) xb (hP _)
  have hlow0 : ∀ i, f i s.1 + ⟪f' i s.1, xs - s.1⟫ + 0 ≤ f i xs := fun i => by
    simpa using sg_grad_ineq (f i) (f' i s.1) s.1 xs (hconv i) (hgrad i s.1)
  have hlow := sg_avg_lower hn f f' s.1 xs 0 hlow0
  rw [add_zero] at hlow
  have hxz := sg_xz (fAvg f) h G Δ s.1 xs w (P w) hγ hγL hL.le hw hlow
    (sg_avg_upper hn f f' s.1 (P w) _ (fun i => sg_descent (f i) (f' i) (hgrad i) L (hLip i) _ _))
    (hvi xs)
  have hfirm := sg_firm h hγ w (s.1 - γ • G) (P w) xb hvi hvib
  have hdiff : w - (s.1 - γ • G) = -(γ • Δ) := by rw [hw]; module
  rw [hdiff] at hfirm
  have hf2 := sg_firm2 _ _ hfirm
  rw [inner_neg_left, inner_smul_left, RCLike.conj_to_real, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hf2
  have hsplit : ⟪Δ, P w - xs⟫ = ⟪Δ, P w - xb⟫ + ⟪Δ, xb - xs⟫ := by
    rw [← inner_add_right]; congr 1; abel
  rw [hsplit] at hxz
  nlinarith

theorem prox_svrg_core {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d))
    {α : ℝ} (hα : 0 < α)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    α * ((1 / (n : ℝ)) * ∑ j, ‖(sagaStep f' P (1 / (3 * L)) s j).1 - xs‖ ^ 2) ≤
      α * ‖s.1 - xs‖ ^ 2
        - 2 * α * (1 / (3 * L)) * ((1 / (n : ℝ)) * ∑ j,
            ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
              - (fAvg f xs + h xs)))
        + 2 * α * (1 / (3 * L)) ^ 2 *
            ((1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' (1 / (3 * L)) s j‖ ^ 2) := by
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    sg_svrg_j hn hL f f' hgrad hLip hconv h hh P hP xs s j)
  have hγ : (1 / (3 * L)) ≠ 0 := by positivity
  have hz : ∑ j, ⟪sagaDelta f' (1 / (3 * L)) s j,
      P (s.1 - (1 / (3 * L)) • gradAvg f' s.1) - xs⟫ = 0 := by
    rw [← sum_inner, sg_delta_sum hn f' hγ s, inner_zero_left]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hz] at hs
  set S := ∑ j, ‖(sagaStep f' P (1 / (3 * L)) s j).1 - xs‖ ^ 2
  set SF := ∑ j, ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1
    + h (sagaStep f' P (1 / (3 * L)) s j).1) - (fAvg f xs + h xs))
  set SN := ∑ j, ‖sagaDelta f' (1 / (3 * L)) s j‖ ^ 2
  have hSF : SF = ∑ x, fAvg f (sagaStep f' P (1 / (3 * L)) s x).1
      + ∑ x, h (sagaStep f' P (1 / (3 * L)) s x).1 - (n * fAvg f xs + n * h xs) := by
    simp only [SF, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ α / n)
  have e : α / n * (n * ‖s.1 - xs‖ ^ 2 - 2 * (1 / (3 * L)) * SF - 2 * (1 / (3 * L)) * 0
      + 2 * (1 / (3 * L)) ^ 2 * SN) = α * ‖s.1 - xs‖ ^ 2
        - 2 * α * (1 / (3 * L)) * ((1 / (n : ℝ)) * SF)
        + 2 * α * (1 / (3 * L)) ^ 2 * ((1 / (n : ℝ)) * SN) := by
    field_simp; ring
  have e2 : α / n * S = α * ((1 / (n : ℝ)) * S) := by ring
  rw [← hSF] at this
  linarith


lemma sg_table {n : ℕ} {β : Type*} (g : Fin n → β → ℝ) (φ : Fin n → β) (x : β) :
    ∑ j, ∑ i, g i (Function.update φ j x i) = ∑ i, g i x + ((n:ℝ) - 1) * ∑ i, g i (φ i) := by
  rw [Finset.sum_comm]
  have per : ∀ i, ∑ j, g i (Function.update φ j x i) = g i x + ((n:ℝ) - 1) * g i (φ i) := by
    intro i
    have : ∀ j, g i (Function.update φ j x i) =
        g i (φ i) + if i = j then g i x - g i (φ i) else 0 := by
      intro j
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_apply, h]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [per, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma sg_lyap {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    lyapunov f f' xs a s = (1 / (n:ℝ)) * ∑ i, (f i (s.2 i) - f i xs - ⟪f' i xs, s.2 i - xs⟫)
      + a * ‖s.1 - xs‖ ^ 2 := by
  unfold lyapunov fAvg
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

lemma sg_var {d n : ℕ} (hn : 0 < n) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∑ j, ‖a j - (1 / (n:ℝ)) • ∑ i, a i‖ ^ 2 ≤ ∑ j, ‖a j‖ ^ 2 := by
  set m := (1 / (n:ℝ)) • ∑ i, a i with hm
  have hN : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, a i = (n:ℝ) • m := by
    rw [hm, smul_smul, mul_one_div_cancel hN, one_smul]
  have e : ∀ j, ‖a j - m‖ ^ 2 = ‖a j‖ ^ 2 - 2 * ⟪a j, m⟫ + ‖m‖ ^ 2 := fun j => norm_sub_sq_real _ _
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← sum_inner]
  rw [hs, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have : (0:ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg ‖m‖]

lemma sg_sq2 {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_sub_sq_real u v, norm_add_sq_real u v, sq_nonneg ‖u + v‖]

theorem lyap_core {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n))
        (sagaStep f' P (1 / (3 * L)) s j)
      - lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n)) s ≤
      -(1 / (4 * (n : ℝ))) * ((1 / (n : ℝ)) * ∑ j,
          ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
            - (fAvg f xs + h xs))) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hNne : (n:ℝ) ≠ 0 := hN.ne'
  have hα : 0 < 3 * L / (8 * n) := by positivity
  have hsvrg := prox_svrg_core hn hL f f' hgrad hLip hconv h hh P hP xs hα s
  set γ := 1 / (3 * L) with hγdef
  have hγ : 0 < γ := by positivity
  set x := s.1 with hx
  set φ := s.2 with hφ
  set G := gradAvg f' x with hG
  set Gs := gradAvg f' xs with hGs
  set r := x - xs with hr
  -- vectors
  set av : Fin n → EuclideanSpace ℝ (Fin d) := fun i => f' i x - f' i xs with hav
  set bv : Fin n → EuclideanSpace ℝ (Fin d) := fun i => f' i (φ i) - f' i xs with hbv
  have hGa : G - Gs = (1 / (n:ℝ)) • ∑ i, av i := by
    simp only [hG, hGs, gradAvg, hav, Finset.sum_sub_distrib, smul_sub]
  have hbbar : (1 / (n:ℝ)) • ∑ i, bv i = (1 / (n:ℝ)) • ∑ i, f' i (φ i) - Gs := by
    simp only [hGs, gradAvg, hbv, Finset.sum_sub_distrib, smul_sub]
  have hu : ∀ j, G + sagaDelta f' γ s j - Gs = av j - (bv j - (1 / (n:ℝ)) • ∑ i, bv i) := by
    intro j
    rw [sg_delta_v f' hγ.ne' s j, hbbar]
    simp only [hav, hbv]
    abel
  have hΔ : ∀ j, sagaDelta f' γ s j = (av j - (1 / (n:ℝ)) • ∑ i, av i)
      - (bv j - (1 / (n:ℝ)) • ∑ i, bv i) := by
    intro j
    rw [sg_delta_v f' hγ.ne' s j, hbbar, ← hGa]
    simp only [hav, hbv]
    abel
  -- c-part per j
  have hoptvi := sg_opt_vi hn hL f f' hgrad hLip h hh xs hopt hγ
  have cj : ∀ j, ‖(sagaStep f' P γ s j).1 - xs‖ ^ 2 ≤
      ‖r‖ ^ 2 - 2 * γ * ⟪G + sagaDelta f' γ s j - Gs, r⟫
        + γ ^ 2 * ‖G + sagaDelta f' γ s j - Gs‖ ^ 2 := by
    intro j
    have hxp : (sagaStep f' P γ s j).1 = P (sagaW f' γ s j) := rfl
    rw [hxp]
    have hvi := sg_prox_vi h hh hγ _ _ (hP (sagaW f' γ s j))
    have hfirm := sg_firm h hγ (sagaW f' γ s j) (xs - γ • Gs) _ xs hvi hoptvi
    have hf2 := sg_firm2 _ _ hfirm
    have hw : sagaW f' γ s j - (xs - γ • Gs) = r - γ • (G + sagaDelta f' γ s j - Gs) := by
      rw [sg_delta_eq f' hγ.ne' s j]; simp only [hr, hx]; module
    rw [hw] at hf2 hfirm
    have hn2 : ‖r - γ • (G + sagaDelta f' γ s j - Gs)‖ ^ 2 = ‖r‖ ^ 2
        - 2 * γ * ⟪G + sagaDelta f' γ s j - Gs, r⟫ + γ ^ 2 * ‖G + sagaDelta f' γ s j - Gs‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
        real_inner_comm]
      ring
    linarith
  have hsumc := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => cj j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumc
  -- inner sum
  have hSI : ∑ j, ⟪G + sagaDelta f' γ s j - Gs, r⟫ = ∑ i, ⟪av i, r⟫ := by
    have e : ∀ j, ⟪G + sagaDelta f' γ s j - Gs, r⟫ = ⟪G - Gs, r⟫ + ⟪sagaDelta f' γ s j, r⟫ := by
      intro j; rw [← inner_add_left]; congr 1; abel
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← sum_inner, sg_delta_sum hn f' hγ.ne' s, inner_zero_left, add_zero, hGa,
      real_inner_smul_left, sum_inner, ← mul_assoc, mul_one_div_cancel hNne, one_mul]
  rw [hSI] at hsumc
  -- variance bounds
  have hSV : ∑ j, ‖G + sagaDelta f' γ s j - Gs‖ ^ 2 ≤ 2 * ∑ i, ‖av i‖ ^ 2 + 2 * ∑ i, ‖bv i‖ ^ 2 := by
    simp only [hu]
    calc ∑ j, ‖av j - (bv j - (1 / (n:ℝ)) • ∑ i, bv i)‖ ^ 2
        ≤ ∑ j, (2 * ‖av j‖ ^ 2 + 2 * ‖bv j - (1 / (n:ℝ)) • ∑ i, bv i‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => sg_sq2 _ _)
      _ = 2 * ∑ j, ‖av j‖ ^ 2 + 2 * ∑ j, ‖bv j - (1 / (n:ℝ)) • ∑ i, bv i‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * ∑ i, ‖av i‖ ^ 2 + 2 * ∑ i, ‖bv i‖ ^ 2 := by
          have := sg_var hn bv; linarith
  have hSD : ∑ j, ‖sagaDelta f' γ s j‖ ^ 2 ≤ 2 * ∑ i, ‖av i‖ ^ 2 + 2 * ∑ i, ‖bv i‖ ^ 2 := by
    simp only [hΔ]
    calc ∑ j, ‖(av j - (1 / (n:ℝ)) • ∑ i, av i) - (bv j - (1 / (n:ℝ)) • ∑ i, bv i)‖ ^ 2
        ≤ ∑ j, (2 * ‖av j - (1 / (n:ℝ)) • ∑ i, av i‖ ^ 2
            + 2 * ‖bv j - (1 / (n:ℝ)) • ∑ i, bv i‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => sg_sq2 _ _)
      _ = 2 * ∑ j, ‖av j - (1 / (n:ℝ)) • ∑ i, av i‖ ^ 2
            + 2 * ∑ j, ‖bv j - (1 / (n:ℝ)) • ∑ i, bv i‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * ∑ i, ‖av i‖ ^ 2 + 2 * ∑ i, ‖bv i‖ ^ 2 := by
          have := sg_var hn bv; have := sg_var hn av; linarith
  -- cocoercivity facts
  have hup := fun i => sg_descent (f i) (f' i) (hgrad i) L (hLip i)
  have hlo := fun i a b => sg_strong_lower (f i) 0 (f' i a) a b
    (strongConvexOn_zero.mpr (hconv i)) (hgrad i a)
  have coc := fun i => sg_cocoer (f i) (f' i) 0 L (hlo i) (hup i)
  set bf : Fin n → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun i y => f i y - f i xs - ⟪f' i xs, y - xs⟫ with hbf
  have hAφ : ∑ i, ‖bv i‖ ^ 2 ≤ 2 * L * ∑ i, bf i (φ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have := coc i xs (φ i)
    simp only [zero_smul, sub_zero, zero_div, zero_mul] at this
    simp only [hbv, hbf]; linarith
  have hBx : ∑ i, bf i x + 1 / (2 * L) * ∑ i, ‖av i‖ ^ 2 ≤ ∑ i, ⟪av i, r⟫ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := coc i x xs
    simp only [zero_smul, sub_zero, zero_div, zero_mul] at this
    rw [norm_sub_rev] at this
    have e : ⟪av i, r⟫ = ⟪f' i x, x - xs⟫ - ⟪f' i xs, x - xs⟫ := by
      simp only [hav, hr, inner_sub_left]
    have e2 : xs - x = -(x - xs) := by abel
    rw [e2, inner_neg_right] at this
    rw [e]
    simp only [hbf, hav]
    have hl : 1 / (2 * L) * ‖f' i x - f' i xs‖ ^ 2 ≤
        f i xs - f i x + ⟪f' i x, x - xs⟫ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
    linarith
  -- rewrite the Lyapunov values
  rw [sg_lyap]
  simp only [sg_lyap, Finset.sum_add_distrib, ← Finset.mul_sum]
  have htab : ∑ j, ∑ i, (f i ((sagaStep f' P γ s j).2 i) - f i xs
      - ⟪f' i xs, (sagaStep f' P γ s j).2 i - xs⟫) =
      ∑ i, bf i x + ((n:ℝ) - 1) * ∑ i, bf i (φ i) := by
    have := sg_table bf φ x
    simpa [sagaStep, hbf] using this
  rw [htab]
  set Sx := ∑ i, ‖av i‖ ^ 2
  set Sp := ∑ i, ‖bv i‖ ^ 2
  set Bx := ∑ i, bf i x
  set Ap := ∑ i, bf i (φ i)
  set SI := ∑ i, ⟪av i, r⟫
  set Ej := ∑ j, ‖(sagaStep f' P γ s j).1 - xs‖ ^ 2
  set SF := ∑ j, ((fAvg f (sagaStep f' P γ s j).1 + h (sagaStep f' P γ s j).1)
            - (fAvg f xs + h xs))
  set SD := ∑ j, ‖sagaDelta f' γ s j‖ ^ 2
  set SV := ∑ j, ‖G + sagaDelta f' γ s j - Gs‖ ^ 2
  have hφ2 : (fun i => s.2 i) = φ := rfl
  -- scaled facts
  have c1 : 3 * L / (2 * n) * Ej ≤ 3 * L / 2 * ‖r‖ ^ 2 - SI / n + SV / (6 * n * L) := by
    have := mul_le_mul_of_nonneg_left hsumc (by positivity : (0:ℝ) ≤ 3 * L / (2 * n))
    have e : 3 * L / (2 * n) * (n * ‖r‖ ^ 2 - 2 * γ * SI + γ ^ 2 * SV) =
        3 * L / 2 * ‖r‖ ^ 2 - SI / n + SV / (6 * n * L) := by
      rw [hγdef]; field_simp; ring
    linarith
  have c2 : SV / (6 * n * L) ≤ (2 * Sx + 2 * Sp) / (6 * n * L) :=
    div_le_div_of_nonneg_right hSV (by positivity)
  have c3 : (Bx + 1 / (2 * L) * Sx) / n ≤ SI / n := div_le_div_of_nonneg_right hBx hN.le
  have c4 : 3 * L / (8 * n) * ((1 / n) * Ej) ≤ 3 * L / 8 * ‖r‖ ^ 2 / n - SF / (4 * n * n)
      + SD / (12 * n * n * L) := by
    have e : 3 * L / (8 * n) * ‖r‖ ^ 2 - 2 * (3 * L / (8 * n)) * γ * (1 / n * SF)
        + 2 * (3 * L / (8 * n)) * γ ^ 2 * (1 / n * SD) =
        3 * L / 8 * ‖r‖ ^ 2 / n - SF / (4 * n * n) + SD / (12 * n * n * L) := by
      rw [hγdef]; field_simp; ring
    linarith
  have hr2 : ‖s.1 - xs‖ = ‖r‖ := rfl
  rw [hr2]
  have f1 : 3 / 2 * (L * Ej / n) ≤ 3 / 2 * (L * ‖r‖ ^ 2) - SI / n + 1 / 6 * (SV / (n * L)) := by
    linarith [c1, show 3 * L / (2 * n) * Ej = 3 / 2 * (L * Ej / n) by ring,
      show SV / (6 * n * L) = 1 / 6 * (SV / (n * L)) by ring,
      show 3 * L / 2 * ‖r‖ ^ 2 = 3 / 2 * (L * ‖r‖ ^ 2) by ring]
  have f2 : SV / (n * L) ≤ 2 * (Sx / (n * L)) + 2 * (Sp / (n * L)) := by
    have := div_le_div_of_nonneg_right hSV (by positivity : (0:ℝ) ≤ n * L)
    linarith [show (2 * Sx + 2 * Sp) / (n * L) = 2 * (Sx / (n * L)) + 2 * (Sp / (n * L)) by ring]
  have f3 : Bx / n + 1 / 2 * (Sx / (n * L)) ≤ SI / n := by
    linarith [c3, show (Bx + 1 / (2 * L) * Sx) / n = Bx / n + 1 / 2 * (Sx / (n * L)) by ring]
  have f4 : 3 / 8 * (L * Ej / n) ≤ 3 / 8 * (L * ‖r‖ ^ 2) - 1 / 4 * (SF / n)
      + 1 / 12 * (SD / (n * L)) := by
    have := mul_le_mul_of_nonneg_left c4 hN.le
    have e1 : (n:ℝ) * (3 * L / (8 * n) * ((1 / n) * Ej)) = 3 / 8 * (L * Ej / n) := by
      field_simp
    have e2 : (n:ℝ) * (3 * L / 8 * ‖r‖ ^ 2 / n - SF / (4 * n * n) + SD / (12 * n * n * L)) =
        3 / 8 * (L * ‖r‖ ^ 2) - 1 / 4 * (SF / n) + 1 / 12 * (SD / (n * L)) := by
      field_simp
    linarith
  have f5 : SD / (n * L) ≤ 2 * (Sx / (n * L)) + 2 * (Sp / (n * L)) := by
    have := div_le_div_of_nonneg_right hSD (by positivity : (0:ℝ) ≤ n * L)
    linarith [show (2 * Sx + 2 * Sp) / (n * L) = 2 * (Sx / (n * L)) + 2 * (Sp / (n * L)) by ring]
  have f6 : Sp / (n * L) ≤ 2 * (Ap / n) := by
    have := div_le_div_of_nonneg_right hAφ (by positivity : (0:ℝ) ≤ n * L)
    have e : 2 * L * Ap / (n * L) = 2 * (Ap / n) := by field_simp
    linarith
  have g1 : Bx / n - Ap / n + 15 / 8 * (L * Ej / n) - 15 / 8 * (L * ‖r‖ ^ 2)
      + 1 / 4 * (SF / n) ≤ 0 := by linarith
  have efin : 1 / ↑n * (1 / ↑n * (Bx + (↑n - 1) * Ap) + (3 * L / (2 * ↑n) + 3 * L / (8 * ↑n)) * Ej) -
      (1 / ↑n * Ap + (3 * L / (2 * ↑n) + 3 * L / (8 * ↑n)) * ‖r‖ ^ 2)
      - -(1 / (4 * ↑n)) * (1 / ↑n * SF) = 1 / n * (Bx / n - Ap / n + 15 / 8 * (L * Ej / n)
        - 15 / 8 * (L * ‖r‖ ^ 2) + 1 / 4 * (SF / n)) := by
    field_simp; ring
  have : 1 / (n:ℝ) * (Bx / n - Ap / n + 15 / 8 * (L * Ej / n)
        - 15 / 8 * (L * ‖r‖ ^ 2) + 1 / 4 * (SF / n)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) g1
  linarith

end SAGA.Convex

open SAGA.Convex


theorem solution {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    (1 / (n : ℝ)) * ∑ j, lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n))
        (sagaStep f' P (1 / (3 * L)) s j)
      - lyapunov f f' xs (3 * L / (2 * n) + 3 * L / (8 * n)) s ≤
      -(1 / (4 * (n : ℝ))) * ((1 / (n : ℝ)) * ∑ j,
          ((fAvg f (sagaStep f' P (1 / (3 * L)) s j).1 + h (sagaStep f' P (1 / (3 * L)) s j).1)
            - (fAvg f xs + h xs))) := by
  exact lyap_core hn hL f f' hgrad hLip hconv h hh P hP xs hopt s
