-- Prove2me | solution 1 for VectorCalculus.conservative_iff_closed_line_integrals_vanish
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:21:55.581881+00:00
-- url     : https://prove2.me/submissions/7f06ba2a-4639-4a84-b3fe-2031ecbfaa92

import Mathlib
import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_conservative

namespace TakagiCex66

noncomputable def S : Set ℝ := Set.range (Int.cast : ℤ → ℝ)

noncomputable def d (x : ℝ) : ℝ := Metric.infDist x S

lemma d_cont : Continuous d := Metric.continuous_infDist_pt S

lemma d_nonneg (x : ℝ) : 0 ≤ d x := Metric.infDist_nonneg

lemma d_le_one (x : ℝ) : d x ≤ 1 := by
  have hm : ((⌊x⌋ : ℤ) : ℝ) ∈ S := ⟨⌊x⌋, rfl⟩
  have := Metric.infDist_le_dist_of_mem (x := x) hm
  rw [Real.dist_eq] at this
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  unfold d; rw [abs_of_nonneg (by linarith)] at this; linarith

lemma d_int (z : ℤ) : d z = 0 := Metric.infDist_zero_of_mem ⟨z, rfl⟩

lemma d_attained (x : ℝ) : ∃ r : ℤ, d x = |x - r| := by
  obtain ⟨y, ⟨r, rfl⟩, hy⟩ :=
    Int.isClosedEmbedding_coe_real.isClosed_range.exists_infDist_eq_dist ⟨0, 0, by simp⟩ x
  exact ⟨r, by rw [d, S, hy, Real.dist_eq]⟩

noncomputable def T (x : ℝ) : ℝ := ∑' k : ℕ, (1/2 : ℝ) ^ k * d (2 ^ k * x)

lemma T_cont : Continuous T := by
  unfold T
  refine continuous_tsum (fun k => continuous_const.mul (d_cont.comp (continuous_const.mul continuous_id)))
    (summable_geometric_two) (fun k x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (d_nonneg _))]
  calc (1/2 : ℝ) ^ k * d (2 ^ k * x) ≤ (1/2) ^ k * 1 :=
        mul_le_mul_of_nonneg_left (d_le_one _) (by positivity)
    _ = (1/2) ^ k := mul_one _

lemma T_dyadic (n : ℕ) (m : ℤ) :
    T (m / 2 ^ n) = ∑ k ∈ Finset.range n, (1/2 : ℝ) ^ k * d (2 ^ k * (m / 2 ^ n)) := by
  unfold T
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have : (2 : ℝ) ^ k * (m / 2 ^ n) = ((m * 2 ^ (k - n) : ℤ) : ℝ) := by
    have h2 : (2 : ℝ) ^ k = 2 ^ (k - n) * 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    push_cast
    rw [h2]; field_simp
  rw [this, d_int, mul_zero]

lemma term_int (n k : ℕ) (hk : k < n) (m : ℤ) :
    ∃ z : ℤ, (2 : ℝ) ^ n * ((1/2 : ℝ) ^ k * d (2 ^ k * (m / 2 ^ n))) = z ∧ Even (z - m) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + (j + 1) := ⟨n - k - 1, by omega⟩
  have hx : (2 : ℝ) ^ k * (m / 2 ^ (k + (j + 1))) = m / 2 ^ (j + 1) := by
    rw [pow_add]; field_simp
  rw [hx]
  obtain ⟨r, hr⟩ := d_attained ((m : ℝ) / 2 ^ (j + 1))
  refine ⟨|m - 2 ^ (j + 1) * r|, ?_, ?_⟩
  · rw [hr]
    have hpos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    have e1 : (2 : ℝ) ^ (k + (j + 1)) * (1 / 2) ^ k = 2 ^ (j + 1) := by
      rw [pow_add, one_div_pow]; field_simp
    rw [← mul_assoc, e1]
    push_cast
    rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos]
    congr 1
    field_simp
  · have he : Even ((2 : ℤ) ^ (j + 1) * r) := by
      rw [pow_succ]; exact ⟨2 ^ j * r, by ring⟩
    rcases abs_cases (m - 2 ^ (j + 1) * r) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; have : m - 2 ^ (j + 1) * r - m = -(2 ^ (j + 1) * r) := by ring
      rw [this]; exact he.neg
    · rw [h]
      have : -(m - 2 ^ (j + 1) * r) - m = 2 ^ (j + 1) * r - 2 * m := by ring
      rw [this]; exact he.sub (even_two_mul m)

lemma sum_int (g : ℕ → ℝ) (m : ℤ) (s : Finset ℕ)
    (h : ∀ k ∈ s, ∃ z : ℤ, g k = z ∧ Even (z - m)) :
    ∃ z : ℤ, ∑ k ∈ s, g k = z ∧ Even (z - s.card * m) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z1, h1, e1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨z2, h2, e2⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine ⟨z1 + z2, ?_, ?_⟩
    · rw [Finset.sum_insert ha, h1, h2]; push_cast; ring
    · rw [Finset.card_insert_of_notMem ha]
      have : z1 + z2 - ((s.card + 1 : ℕ) : ℤ) * m = (z1 - m) + (z2 - s.card * m) := by
        push_cast; ring
      rw [this]; exact e1.add e2

lemma W_int (N : ℕ) (m : ℤ) : ∃ z : ℤ, (2 : ℝ) ^ N * T (m / 2 ^ N) = z ∧ Even (z - N * m) := by
  rw [T_dyadic, Finset.mul_sum]
  obtain ⟨z, hz, he⟩ := sum_int _ m (Finset.range N)
    (fun k hk => term_int N k (Finset.mem_range.1 hk) m)
  exact ⟨z, hz, by simpa using he⟩

lemma slope_int (N : ℕ) (m : ℤ) :
    ∃ z : ℤ, (2 : ℝ) ^ N * (T ((m + 1 : ℤ) / 2 ^ N) - T (m / 2 ^ N)) = z ∧ Even (z - N) := by
  obtain ⟨z1, h1, e1⟩ := W_int N (m + 1)
  obtain ⟨z2, h2, e2⟩ := W_int N m
  refine ⟨z1 - z2, by rw [mul_sub, h1, h2]; push_cast; ring, ?_⟩
  have : z1 - z2 - N = (z1 - N * (m + 1)) - (z2 - N * m) := by ring
  rw [this]; exact e1.sub e2

lemma straddle {f : ℝ → ℝ} {L x : ℝ} (hf : HasDerivAt f L x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u v, u ≤ x → x ≤ v → v - u < δ → |f v - f u - L * (v - u)| ≤ ε * (v - u) := by
  have h := (hasDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun u v hu hv huv => ?_⟩
  have hu' := hb (y := u) (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
  have hv' := hb (y := v) (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  simp only [Real.norm_eq_abs, smul_eq_mul] at hu' hv'
  rw [abs_of_nonpos (by linarith : u - x ≤ 0)] at hu'
  rw [abs_of_nonneg (by linarith : 0 ≤ v - x)] at hv'
  have : f v - f u - L * (v - u) = (f v - f x - (v - x) * L) - (f u - f x - (u - x) * L) := by ring
  rw [this]
  calc _ ≤ |f v - f x - (v - x) * L| + |f u - f x - (u - x) * L| := abs_sub _ _
    _ ≤ ε * (v - x) + ε * -(u - x) := add_le_add hv' hu'
    _ = ε * (v - u) := by ring

lemma T_not_diff (x : ℝ) : ¬ DifferentiableAt ℝ T x := by
  intro hd
  obtain ⟨δ, hδ, hb⟩ := straddle hd.hasDerivAt (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1/2 : ℝ) < 1)
  have key : ∀ N : ℕ, n ≤ N → ∃ z : ℤ, |(z : ℝ) - deriv T x| ≤ 1/4 ∧ Even (z - N) := by
    intro N hN
    set m := ⌊(2 : ℝ) ^ N * x⌋
    obtain ⟨z, hz, he⟩ := slope_int N m
    refine ⟨z, ?_, he⟩
    have hpos : (0 : ℝ) < 2 ^ N := by positivity
    have h1 := Int.floor_le ((2 : ℝ) ^ N * x)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ N * x)
    have hu : (m : ℝ) / 2 ^ N ≤ x := by rw [div_le_iff₀ hpos]; linarith
    have hv : x ≤ ((m + 1 : ℤ) : ℝ) / 2 ^ N := by rw [le_div_iff₀ hpos]; push_cast; linarith
    have hw : ((m + 1 : ℤ) : ℝ) / 2 ^ N - m / 2 ^ N = (1/2) ^ N := by
      push_cast; rw [one_div_pow]; field_simp; ring
    have hsmall : (1/2 : ℝ) ^ N ≤ (1/2) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
    have := hb _ _ hu hv (by rw [hw]; linarith)
    rw [hw] at this
    have e : (z : ℝ) - deriv T x = 2 ^ N * (T ((m + 1 : ℤ) / 2 ^ N) - T (m / 2 ^ N) - deriv T x * (1/2) ^ N) := by
      rw [← hz, one_div_pow]; field_simp
    rw [e, abs_mul, abs_of_pos hpos]
    calc 2 ^ N * |T ((m + 1 : ℤ) / 2 ^ N) - T (m / 2 ^ N) - deriv T x * (1/2) ^ N|
        ≤ 2 ^ N * (1/4 * (1/2) ^ N) := mul_le_mul_of_nonneg_left this hpos.le
      _ = 1/4 := by rw [one_div_pow]; field_simp
  obtain ⟨z1, h1, e1⟩ := key n le_rfl
  obtain ⟨z2, h2, e2⟩ := key (n + 1) (Nat.le_succ n)
  have hle : |((z1 - z2 : ℤ) : ℝ)| ≤ 1/2 := by
    push_cast
    calc |(z1 : ℝ) - z2| = |((z1 : ℝ) - deriv T x) - ((z2 : ℝ) - deriv T x)| := by ring_nf
      _ ≤ |(z1 : ℝ) - deriv T x| + |(z2 : ℝ) - deriv T x| := abs_sub _ _
      _ ≤ 1/2 := by linarith
  have hz : z1 = z2 := by
    have : |z1 - z2| < 1 := by
      have : (|z1 - z2| : ℝ) < 1 := by rw [← Int.cast_abs] at hle; push_cast at hle ⊢; linarith
      exact_mod_cast this
    have := abs_lt.1 this
    omega
  subst hz
  have : Even (((n : ℤ) + 1) - n) := by
    have := e1.sub e2
    have h : z1 - (n : ℤ) - (z1 - ((n + 1 : ℕ) : ℤ)) = ((n : ℤ) + 1) - n := by push_cast; ring
    rwa [h] at this
  simp at this

end TakagiCex66

open VectorCalculus in
theorem cex_conservative_66 :
    IsConservative (fun p : Fin 2 → ℝ => fun i : Fin 2 => if i = 0 then p 1 else 0) := by
  refine ⟨fun p => p 0 * p 1 + TakagiCex66.T (p 1), ?_, ?_⟩
  · exact ((continuous_apply 0).mul (continuous_apply 1)).add
      (TakagiCex66.T_cont.comp (continuous_apply 1))
  · intro y
    funext i
    simp only [grad, partialDeriv]
    fin_cases i
    · have hf : (fun s : ℝ => Function.update y 0 s 0 * Function.update y 0 s 1 +
          TakagiCex66.T (Function.update y 0 s 1)) = fun s => s * y 1 + TakagiCex66.T (y 1) := by
        funext s; simp
      simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      rw [hf]
      have := (((hasDerivAt_id' (y 0)).mul_const (y 1)).add_const (TakagiCex66.T (y 1))).deriv
      rw [this]; simp
    · have hf : (fun s : ℝ => Function.update y 1 s 0 * Function.update y 1 s 1 +
          TakagiCex66.T (Function.update y 1 s 1)) = fun s => y 0 * s + TakagiCex66.T s := by
        funext s; simp
      simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [hf, deriv_zero_of_not_differentiableAt]
      intro hd
      apply TakagiCex66.T_not_diff (y 1)
      have h2 : DifferentiableAt ℝ (fun s : ℝ => y 0 * s) (y 1) :=
        (differentiableAt_id).const_mul (y 0)
      have := hd.sub h2
      have e : ((fun s : ℝ => y 0 * s + TakagiCex66.T s) - fun s => y 0 * s) = TakagiCex66.T := by
        funext s; simp
      rwa [e] at this

open VectorCalculus in
theorem cex_loop_66 :
    lineIntegral (fun p : Fin 2 → ℝ => fun i : Fin 2 => if i = 0 then p 1 else 0)
      (fun t => fun i : Fin 2 => if i = 0 then Real.cos t else Real.sin t) 0 (2 * Real.pi)
      = -Real.pi := by
  unfold lineIntegral
  have h : ∀ t : ℝ, (∑ i : Fin 2,
      (fun p : Fin 2 → ℝ => fun i : Fin 2 => if i = 0 then p 1 else 0)
        ((fun t => fun i : Fin 2 => if i = 0 then Real.cos t else Real.sin t) t) i *
      deriv (fun s => (fun t => fun i : Fin 2 => if i = 0 then Real.cos t else Real.sin t) s i) t)
      = -(Real.sin t ^ 2) := by
    intro t
    simp [Real.deriv_cos']
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_neg, integral_sin_sq]
  simp

open VectorCalculus in
theorem solution : ¬ (∀ {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : Continuous F),
    (∀ (x : ℝ → (Fin n → ℝ)) (a b : ℝ), a ≤ b → ContDiff ℝ 1 x → x a = x b →
      lineIntegral F x a b = 0) ↔ IsConservative F) := by
  intro h
  have hF : Continuous (fun p : Fin 2 → ℝ => fun i : Fin 2 => if i = 0 then p 1 else 0) := by
    apply continuous_pi; intro i
    split_ifs
    · exact continuous_apply 1
    · exact continuous_const
  have hall := (h _ hF).2 cex_conservative_66
  have hx : ContDiff ℝ 1 (fun t => fun i : Fin 2 => if i = 0 then Real.cos t else Real.sin t) := by
    apply contDiff_pi.2; intro i
    split_ifs
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
  have := hall _ 0 (2 * Real.pi) (by positivity) hx (by funext i; simp)
  rw [cex_loop_66] at this
  exact Real.pi_ne_zero (neg_eq_zero.1 this)
