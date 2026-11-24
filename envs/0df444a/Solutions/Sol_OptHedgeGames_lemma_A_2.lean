-- Prove2me | solution 1 for OptHedgeGames.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:25:45.656504+00:00
-- url     : https://prove2.me/submissions/9629676a-9ecd-4ede-8bae-c214827421b8

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace SolOHGA2

open OptHedgeGames

variable {n : ℕ}

/-- The straight path `t ↦ w + t d`. -/
def xt (w d : Fin n → ℝ) (t : ℝ) : Fin n → ℝ := fun c => w c + t * d c

lemma exists_pos {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ a, 0 < p a := by
  by_contra h
  push_neg at h
  have : ∑ a, p a ≤ 0 := Finset.sum_nonpos fun a _ => h a
  linarith

lemma Z_pos {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (x : Fin n → ℝ) :
    0 < ∑ c, p c * Real.exp (x c) := by
  obtain ⟨a, ha⟩ := exists_pos hp0 hp1
  calc 0 < p a * Real.exp (x a) := mul_pos ha (Real.exp_pos _)
    _ ≤ ∑ c, p c * Real.exp (x c) :=
      Finset.single_le_sum (f := fun c => p c * Real.exp (x c))
        (fun c _ => mul_nonneg (hp0 c) (Real.exp_pos _).le) (Finset.mem_univ a)

lemma tilt_nonneg {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (x : Fin n → ℝ) (a : Fin n) : 0 ≤ tilt p x a := by
  unfold tilt
  exact div_nonneg (mul_nonneg (hp0 a) (Real.exp_pos _).le) (Z_pos hp0 hp1 x).le

lemma tilt_sum {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (x : Fin n → ℝ) : ∑ a, tilt p x a = 1 := by
  unfold tilt
  rw [← Finset.sum_div, div_self (Z_pos hp0 hp1 x).ne']

lemma tilt_zero {p : Fin n → ℝ} (hp1 : ∑ a, p a = 1) : tilt p (fun _ => 0) = p := by
  funext a
  simp [tilt, hp1]

lemma tilt_ratio {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (x : Fin n → ℝ) (lo hi : ℝ) (hx : ∀ a, lo ≤ x a ∧ x a ≤ hi) (a : Fin n) :
    tilt p x a ≤ Real.exp (hi - lo) * p a ∧ Real.exp (-(hi - lo)) * p a ≤ tilt p x a := by
  have hZ := Z_pos hp0 hp1 x
  have hZlo : Real.exp lo ≤ ∑ c, p c * Real.exp (x c) := by
    calc Real.exp lo = ∑ c, p c * Real.exp lo := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hx c).1) (hp0 c)
  have hZhi : ∑ c, p c * Real.exp (x c) ≤ Real.exp hi := by
    calc _ ≤ ∑ c, p c * Real.exp hi := Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hx c).2) (hp0 c)
      _ = Real.exp hi := by rw [← Finset.sum_mul, hp1, one_mul]
  have elo := Real.exp_pos lo
  have ehi := Real.exp_pos hi
  unfold tilt
  constructor
  · rw [div_le_iff₀ hZ]
    calc p a * Real.exp (x a) ≤ p a * Real.exp hi :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hx a).2) (hp0 a)
      _ = Real.exp (hi - lo) * p a * Real.exp lo := by
          rw [Real.exp_sub]; field_simp
      _ ≤ Real.exp (hi - lo) * p a * ∑ c, p c * Real.exp (x c) :=
          mul_le_mul_of_nonneg_left hZlo (mul_nonneg (Real.exp_pos _).le (hp0 a))
  · rw [le_div_iff₀ hZ]
    calc Real.exp (-(hi - lo)) * p a * ∑ c, p c * Real.exp (x c)
        ≤ Real.exp (-(hi - lo)) * p a * Real.exp hi :=
          mul_le_mul_of_nonneg_left hZhi (mul_nonneg (Real.exp_pos _).le (hp0 a))
      _ = p a * Real.exp lo := by
          rw [show -(hi - lo) = lo - hi by ring, Real.exp_sub]; field_simp
      _ ≤ p a * Real.exp (x a) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hx a).1) (hp0 a)

lemma var_le_sum (q v : Fin n → ℝ) (hq1 : ∑ a, q a = 1) (c : ℝ) :
    var q v ≤ ∑ a, q a * (v a - c) ^ 2 := by
  unfold var
  have e : ∀ a, q a * (v a - c) ^ 2 = q a * (v a - ∑ c, q c * v c) ^ 2 +
      (2 * ((∑ c, q c * v c) - c)) * (q a * v a) -
      (((∑ c, q c * v c) - c) * ((∑ c, q c * v c) + c)) * q a := fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hq1]
  nlinarith [sq_nonneg ((∑ c, q c * v c) - c)]

lemma var_le_of_le (p q v : Fin n → ℝ) (K : ℝ) (hq1 : ∑ a, q a = 1)
    (hle : ∀ a, q a ≤ K * p a) : var q v ≤ K * var p v := by
  calc var q v ≤ ∑ a, q a * (v a - ∑ c, p c * v c) ^ 2 := var_le_sum q v hq1 _
    _ ≤ ∑ a, K * p a * (v a - ∑ c, p c * v c) ^ 2 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hle a) (sq_nonneg _)
    _ = K * var p v := by
        unfold var
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring

lemma wcs (q x y : Fin n → ℝ) (hq0 : ∀ a, 0 ≤ q a) :
    ∑ a, q a * x a * y a ≤
      Real.sqrt (∑ a, q a * x a ^ 2) * Real.sqrt (∑ a, q a * y a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (q a) * x a)
    (fun a => Real.sqrt (q a) * y a)
  have e1 : ∀ a, Real.sqrt (q a) * x a * (Real.sqrt (q a) * y a) = q a * x a * y a := fun a => by
    rw [show Real.sqrt (q a) * x a * (Real.sqrt (q a) * y a) =
      (Real.sqrt (q a) * Real.sqrt (q a)) * x a * y a by ring, Real.mul_self_sqrt (hq0 a)]
  have e2 : ∀ (u : Fin n → ℝ) a, (Real.sqrt (q a) * u a) ^ 2 = q a * u a ^ 2 := fun u a => by
    rw [mul_pow, Real.sq_sqrt (hq0 a)]
  simp only [e1, e2] at h
  have hA : 0 ≤ ∑ a, q a * x a ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (sq_nonneg _)
  rw [← Real.sqrt_mul hA]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

lemma cov_bound (q s d : Fin n → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1)
    (hs : ∀ a, s a ^ 2 = 1) (c0 : ℝ) :
    ∑ a, s a * (q a * (d a - ∑ c, q c * d c)) ≤ Real.sqrt (∑ a, q a * (d a - c0) ^ 2) := by
  have key : ∑ a, s a * (q a * (d a - ∑ c, q c * d c)) =
      ∑ a, q a * (s a - ∑ c, q c * s c) * (d a - c0) := by
    have e1 : ∀ a, s a * (q a * (d a - ∑ c, q c * d c)) =
        q a * s a * d a - (∑ c, q c * d c) * (q a * s a) := fun a => by ring
    have e2 : ∀ a, q a * (s a - ∑ c, q c * s c) * (d a - c0) =
        q a * s a * d a - c0 * (q a * s a) - (∑ c, q c * s c) * (q a * d a) +
          (∑ c, q c * s c) * c0 * q a := fun a => by ring
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_congr rfl fun a _ => e2 a,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hq1]
    ring
  rw [key]
  have hvs : Real.sqrt (∑ a, q a * (s a - ∑ c, q c * s c) ^ 2) ≤ 1 := by
    have h1 : ∑ a, q a * (s a - ∑ c, q c * s c) ^ 2 ≤ 1 := by
      have := var_le_sum q s hq1 0
      unfold var at this
      simp only [sub_zero, hs, mul_one, hq1] at this
      exact this
    calc _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  calc _ ≤ Real.sqrt (∑ a, q a * (s a - ∑ c, q c * s c) ^ 2) *
        Real.sqrt (∑ a, q a * (d a - c0) ^ 2) :=
        wcs q (fun a => s a - ∑ c, q c * s c) (fun a => d a - c0) hq0
    _ ≤ 1 * Real.sqrt (∑ a, q a * (d a - c0) ^ 2) :=
        mul_le_mul_of_nonneg_right hvs (Real.sqrt_nonneg _)
    _ = _ := one_mul _

lemma hasDerivAt_Z (p w d : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ c, p c * Real.exp (xt w d t c))
      (∑ c, p c * (Real.exp (xt w d t c) * d c)) t := by
  apply HasDerivAt.fun_sum
  intro c _
  unfold xt
  exact (((hasDerivAt_mul_const (d c)).const_add (w c)).exp).const_mul (p c)

lemma hasDerivAt_tilt {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (w d : Fin n → ℝ) (t : ℝ) (a : Fin n) :
    HasDerivAt (fun t => tilt p (xt w d t) a)
      (tilt p (xt w d t) a * (d a - ∑ c, tilt p (xt w d t) c * d c)) t := by
  have hZ := Z_pos hp0 hp1 (xt w d t)
  have hN : HasDerivAt (fun t => p a * Real.exp (xt w d t a))
      (p a * (Real.exp (xt w d t a) * d a)) t := by
    unfold xt
    exact (((hasDerivAt_mul_const (d a)).const_add (w a)).exp).const_mul (p a)
  have h := hN.div (hasDerivAt_Z p w d t) hZ.ne'
  unfold tilt
  refine h.congr_deriv ?_
  have hs : ∑ c, p c * Real.exp (xt w d t c) / (∑ c, p c * Real.exp (xt w d t c)) * d c =
      (∑ c, p c * (Real.exp (xt w d t c) * d c)) / ∑ c, p c * Real.exp (xt w d t c) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hs]
  field_simp

/-- The `ℓ₁` distance between the endpoints of a tilt path is bounded by a bound on the
derivative of every signed sum. -/
lemma l1_path {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (w d : Fin n → ℝ) (B : ℝ)
    (hB : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ s : Fin n → ℝ, (∀ a, s a ^ 2 = 1) →
      ∑ a, s a * (tilt p (xt w d t) a * (d a - ∑ c, tilt p (xt w d t) c * d c)) ≤ B) :
    l1Norm (tilt p (xt w d 1) - tilt p (xt w d 0)) ≤ B := by
  set s : Fin n → ℝ := fun a =>
    if 0 ≤ tilt p (xt w d 1) a - tilt p (xt w d 0) a then 1 else -1 with hs_def
  have hs : ∀ a, s a ^ 2 = 1 := fun a => by
    simp only [hs_def]; split_ifs <;> norm_num
  have hF : ∀ t, HasDerivAt (fun t => ∑ a, s a * tilt p (xt w d t) a)
      (∑ a, s a * (tilt p (xt w d t) a * (d a - ∑ c, tilt p (xt w d t) c * d c))) t :=
    fun t => HasDerivAt.fun_sum fun a _ => (hasDerivAt_tilt hp0 hp1 w d t a).const_mul (s a)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one
    (fun x _ => (hF x).continuousAt.continuousWithinAt) (fun x _ => hF x)
  have hl1 : l1Norm (tilt p (xt w d 1) - tilt p (xt w d 0)) =
      (∑ a, s a * tilt p (xt w d 1) a) - ∑ a, s a * tilt p (xt w d 0) a := by
    unfold l1Norm
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply, hs_def]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  rw [hl1]
  have := hB ξ hξ s hs
  rw [sub_zero, div_one] at hξeq
  rw [← hξeq]
  exact this

/-- Second-order bounds from bounds on the second derivative (two mean value steps). -/
lemma taylor2 (ψ G H : ℝ → ℝ) (hψ : ∀ t, HasDerivAt ψ (G t) t) (hG : ∀ t, HasDerivAt G (H t) t)
    (hG0 : G 0 = 0) (c C : ℝ) (hH : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ H t ∧ H t ≤ C) :
    c / 2 ≤ ψ 1 - ψ 0 ∧ ψ 1 - ψ 0 ≤ C / 2 := by
  have hGt : ∀ t ∈ Set.Icc (0 : ℝ) 1, c * t ≤ G t ∧ G t ≤ C * t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0; simp [hG0]
    · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope G H hpos
        (fun x _ => (hG x).continuousAt.continuousWithinAt) (fun x _ => hG x)
      have hξ' : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨hξ.1.le, hξ.2.le.trans ht.2⟩
      rw [hG0, sub_zero, sub_zero] at hξeq
      have := hH ξ hξ'
      rw [hξeq, le_div_iff₀ hpos, div_le_iff₀ hpos] at this
      exact this
  have hh : ∀ K : ℝ, ∀ t, HasDerivAt (fun t => ψ t - K * (t * t) / 2) (G t - K * t) t := by
    intro K t
    have := (hψ t).sub ((((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul K).div_const 2)
    exact this.congr_deriv (by simp only [id]; ring)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one
    (fun x _ => (hh c x).continuousAt.continuousWithinAt) (fun x _ => hh c x)
  obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one
    (fun x _ => (hh C x).continuousAt.continuousWithinAt) (fun x _ => hh C x)
  beta_reduce at hξeq hηeq
  rw [sub_zero, div_one] at hξeq hηeq
  have h1 := hGt ξ ⟨hξ.1.le, hξ.2.le⟩
  have h2 := hGt η ⟨hη.1.le, hη.2.le⟩
  constructor
  · nlinarith [h1.1]
  · nlinarith [h2.2]

lemma xt_one (w z : Fin n → ℝ) : xt w (z - w) 1 = z := by
  funext c; simp [xt]

lemma xt_zero (w d : Fin n → ℝ) : xt w d 0 = w := by
  funext c; simp [xt]

lemma xt_zero' (z : Fin n → ℝ) : xt 0 z 0 = fun _ => 0 := by
  funext c; simp [xt]

lemma xt_one' (z : Fin n → ℝ) : xt 0 z 1 = z := by
  funext c; simp [xt]

end SolOHGA2

open OptHedgeGames SolOHGA2 in
theorem solution {n : ℕ} (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (z : Fin n → ℝ) (r : ℝ)
    (hr : osc z ≤ r) :
    (∀ a, 0 < p a → Real.exp (-r) ≤ tilt p z a / p a ∧ tilt p z a / p a ≤ Real.exp r) ∧
      (∀ w : Fin n → ℝ, Real.exp (-r) * var p w ≤ var (tilt p z) w ∧
        var (tilt p z) w ≤ Real.exp r * var p w) ∧
      l1Norm (tilt p z - p) ≤ Real.exp (r / 2) * vnorm p z ∧
      (∀ w : Fin n → ℝ, l1Norm (tilt p z - tilt p w) ≤ ‖z - w‖) ∧
      (1 / 2 * Real.exp (-r) * var p z ≤ kl p (tilt p z) ∧
        kl p (tilt p z) ≤ 1 / 2 * Real.exp r * var p z) := by
  have hp0 : ∀ a, 0 ≤ p a := hp.1
  have hp1 : ∑ a, p a = 1 := hp.2
  set m := ⨅ a, z a with hm
  set M := ⨆ a, z a with hM
  have hzb : ∀ a, m ≤ z a ∧ z a ≤ M := fun a =>
    ⟨ciInf_le (Finite.bddBelow_range z) a, le_ciSup (Finite.bddAbove_range z) a⟩
  have hosc : M - m ≤ r := hr
  have hMm : 0 ≤ M - m := by
    obtain ⟨a, _⟩ := exists_pos hp0 hp1
    linarith [hzb a]
  -- ratio bounds along the path `t ↦ t z`, `t ∈ [0, 1]`
  have ratio_t : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ a,
      tilt p (xt 0 z t) a ≤ Real.exp r * p a ∧ p a ≤ Real.exp r * tilt p (xt 0 z t) a := by
    intro t ht a
    have hx : ∀ c, t * m ≤ xt 0 z t c ∧ xt 0 z t c ≤ t * M := fun c => by
      simp only [xt, Pi.zero_apply, zero_add]
      exact ⟨mul_le_mul_of_nonneg_left (hzb c).1 ht.1, mul_le_mul_of_nonneg_left (hzb c).2 ht.1⟩
    have hle : t * M - t * m ≤ r := by
      have : t * (M - m) ≤ 1 * (M - m) := mul_le_mul_of_nonneg_right ht.2 hMm
      linarith
    obtain ⟨h1, h2⟩ := tilt_ratio hp0 hp1 _ _ _ hx a
    have he : Real.exp (t * M - t * m) ≤ Real.exp r := Real.exp_le_exp.2 hle
    constructor
    · exact h1.trans (mul_le_mul_of_nonneg_right he (hp0 a))
    · have h3 : p a = Real.exp (t * M - t * m) * (Real.exp (-(t * M - t * m)) * p a) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      calc p a = _ := h3
        _ ≤ Real.exp (t * M - t * m) * tilt p (xt 0 z t) a :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ ≤ Real.exp r * tilt p (xt 0 z t) a :=
            mul_le_mul_of_nonneg_right he (tilt_nonneg hp0 hp1 _ a)
  have r1 : ∀ a, tilt p z a ≤ Real.exp r * p a ∧ p a ≤ Real.exp r * tilt p z a := by
    intro a
    have := ratio_t 1 ⟨zero_le_one, le_rfl⟩ a
    rwa [xt_one'] at this
  have hvar_t : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Fin n → ℝ,
      Real.exp (-r) * var p v ≤ var (tilt p (xt 0 z t)) v ∧
        var (tilt p (xt 0 z t)) v ≤ Real.exp r * var p v := by
    intro t ht v
    constructor
    · have := var_le_of_le (tilt p (xt 0 z t)) p v (Real.exp r) hp1 (fun a => (ratio_t t ht a).2)
      have h2 : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      calc Real.exp (-r) * var p v ≤ Real.exp (-r) * (Real.exp r * var (tilt p (xt 0 z t)) v) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = var (tilt p (xt 0 z t)) v := by rw [← mul_assoc, h2, one_mul]
    · exact var_le_of_le p (tilt p (xt 0 z t)) v (Real.exp r) (tilt_sum hp0 hp1 _)
        (fun a => (ratio_t t ht a).1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- (i)
  · intro a ha
    constructor
    · rw [le_div_iff₀ ha]
      have h := (r1 a).2
      have h2 : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      calc Real.exp (-r) * p a ≤ Real.exp (-r) * (Real.exp r * tilt p z a) :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
        _ = tilt p z a := by rw [← mul_assoc, h2, one_mul]
    · rw [div_le_iff₀ ha]; exact (r1 a).1
  -- (ii)
  · intro w
    have := hvar_t 1 ⟨zero_le_one, le_rfl⟩ w
    rwa [xt_one'] at this
  -- (iii)
  · have h := l1_path hp0 hp1 0 z (Real.exp (r / 2) * vnorm p z) (by
      intro t ht s hs
      have hq0 := tilt_nonneg hp0 hp1 (xt 0 z t)
      have hq1 := tilt_sum hp0 hp1 (xt 0 z t)
      refine le_trans (cov_bound _ s z hq0 hq1 hs (∑ c, tilt p (xt 0 z t) c * z c)) ?_
      have hv := (hvar_t t ⟨ht.1.le, ht.2.le⟩ z).2
      unfold var at hv
      unfold vnorm
      calc Real.sqrt (∑ a, tilt p (xt 0 z t) a * (z a - ∑ c, tilt p (xt 0 z t) c * z c) ^ 2)
          ≤ Real.sqrt (Real.exp r * var p z) := Real.sqrt_le_sqrt hv
        _ = Real.exp (r / 2) * Real.sqrt (var p z) := by
          rw [Real.sqrt_mul (Real.exp_pos _).le]
          congr 1
          rw [show r = r / 2 + r / 2 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
          ring_nf)
    rwa [xt_one', xt_zero', tilt_zero hp1] at h
  -- (iv)
  · intro w
    have h := l1_path hp0 hp1 w (z - w) ‖z - w‖ (by
      intro t ht s hs
      have hq0 := tilt_nonneg hp0 hp1 (xt w (z - w) t)
      have hq1 := tilt_sum hp0 hp1 (xt w (z - w) t)
      refine le_trans (cov_bound _ s (z - w) hq0 hq1 hs 0) ?_
      have hb : ∀ a, ((z - w) a - 0) ^ 2 ≤ ‖z - w‖ ^ 2 := fun a => by
        rw [sub_zero, ← sq_abs]
        have : |(z - w) a| ≤ ‖z - w‖ := by
          have := norm_le_pi_norm (z - w) a
          rwa [Real.norm_eq_abs] at this
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      calc Real.sqrt (∑ a, tilt p (xt w (z - w) t) a * ((z - w) a - 0) ^ 2)
          ≤ Real.sqrt (∑ a, tilt p (xt w (z - w) t) a * ‖z - w‖ ^ 2) :=
            Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ =>
              mul_le_mul_of_nonneg_left (hb a) (hq0 a))
        _ = ‖z - w‖ := by
            rw [← Finset.sum_mul, hq1, one_mul, Real.sqrt_sq (norm_nonneg _)])
    rwa [xt_one, xt_zero] at h
  -- (v)
  · set E := ∑ c, p c * z c with hE
    set ψ : ℝ → ℝ := fun t => Real.log (∑ c, p c * Real.exp (xt 0 z t c)) - t * E with hψ_def
    set G : ℝ → ℝ := fun t => ∑ c, tilt p (xt 0 z t) c * z c - E with hG_def
    set H : ℝ → ℝ := fun t => var (tilt p (xt 0 z t)) z with hH_def
    have hψ : ∀ t, HasDerivAt ψ (G t) t := by
      intro t
      have h1 := (hasDerivAt_Z p 0 z t).log (Z_pos hp0 hp1 _).ne'
      have h2 := h1.sub (hasDerivAt_mul_const E)
      refine h2.congr_deriv ?_
      show _ = ∑ c, tilt p (xt 0 z t) c * z c - E
      congr 1
      unfold tilt
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hG : ∀ t, HasDerivAt G (H t) t := by
      intro t
      have h1 : HasDerivAt (fun t => ∑ c, tilt p (xt 0 z t) c * z c)
          (∑ c, tilt p (xt 0 z t) c * (z c - ∑ c', tilt p (xt 0 z t) c' * z c') * z c) t :=
        HasDerivAt.fun_sum fun c _ => (hasDerivAt_tilt hp0 hp1 0 z t c).mul_const (z c)
      have h2 := h1.sub_const E
      refine h2.congr_deriv ?_
      show _ = var (tilt p (xt 0 z t)) z
      unfold var
      have hq1 := tilt_sum hp0 hp1 (xt 0 z t)
      set q := tilt p (xt 0 z t)
      set μ := ∑ c', q c' * z c'
      have e : ∀ c, q c * (z c - μ) * z c = q c * (z c - μ) ^ 2 + μ * (q c * z c) - μ * μ * q c :=
        fun c => by ring
      rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hq1]
      ring
    have hG0 : G 0 = 0 := by
      simp only [hG_def, xt_zero', tilt_zero hp1, hE, sub_self]
    have hHb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.exp (-r) * var p z ≤ H t ∧ H t ≤ Real.exp r * var p z := fun t ht =>
      hvar_t t ht z
    have hT := taylor2 ψ G H hψ hG hG0 _ _ hHb
    have hψ0 : ψ 0 = 0 := by
      simp only [hψ_def, xt_zero']
      simp [hp1]
    have hψ1 : ψ 1 = kl p (tilt p z) := by
      simp only [hψ_def, xt_one', one_mul]
      unfold kl
      have hZ := Z_pos hp0 hp1 z
      have e : ∀ a, p a * Real.log (p a / tilt p z a) =
          Real.log (∑ c, p c * Real.exp (z c)) * p a - p a * z a := by
        intro a
        rcases eq_or_lt_of_le (hp0 a) with h0 | hpos
        · rw [← h0]; ring
        · have : p a / tilt p z a = (∑ c, p c * Real.exp (z c)) / Real.exp (z a) := by
            unfold tilt
            field_simp
          rw [this, Real.log_div hZ.ne' (Real.exp_pos _).ne', Real.log_exp]
          ring
      rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1,
        mul_one]
    rw [hψ0, sub_zero, hψ1] at hT
    constructor
    · linarith [hT.1]
    · linarith [hT.2]
