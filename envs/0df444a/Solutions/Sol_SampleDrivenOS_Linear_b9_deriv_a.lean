-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_deriv_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:01:42.773985+00:00
-- url     : https://prove2.me/submissions/0c30e17b-39ca-42c6-b29d-3b9e569e850a

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

set_option autoImplicit false
open SampleDrivenOS.Linear

lemma da_w_le_one {p : ℝ} (hp0 : 0 ≤ p) (k : ℕ) :
    p ^ k * (1 + (k : ℝ) * (1 - p)) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : p ^ k * (1 + (k : ℝ) * (1 - p)) - p ^ (k + 1) * (1 + ((k + 1 : ℕ) : ℝ) * (1 - p))
        = p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by push_cast; ring
    have : 0 ≤ p ^ k * (1 - p) ^ 2 * ((k : ℝ) + 1) := by positivity
    linarith

lemma da_w_bounds {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (i : ℕ) :
    0 ≤ p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) ∧
      p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have : 0 ≤ 1 - p := by linarith
    positivity
  · have := da_w_le_one hp0.le (i + 1)
    push_cast at this
    exact this

lemma da_summable_inv : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) this
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- the denominator `D_i(x) = 1/x - s (1 - w_i(x))` lies in `[1/x - s, 1/x]`. -/
lemma da_D_bounds {s x : ℝ} (hs0 : 0 < s) (hx0 : 0 < x) (hx1 : x ≤ 1) (i : ℕ) :
    1 / x - s ≤ 1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x))) ∧
      1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x))) ≤ 1 / x := by
  obtain ⟨h0, h1⟩ := da_w_bounds hx0 hx1 i
  constructor <;> nlinarith

lemma da_term_deriv (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (i : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt (fun y : ℝ => Real.log (1 / y - s * (1 - y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2)))
      ((-1 / x ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (x ^ i - x ^ (i + 1))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x)))))) x := by
  have hD : 0 < 1 / x - s * (1 - x ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - x))) := by
    have h1 := (da_D_bounds hs0 hx0 hx1 i).1
    have : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
    linarith
  have hw : HasDerivAt (fun y : ℝ => y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y)))
      (((i + 1 : ℕ) : ℝ) * x ^ i * (1 + ((i : ℝ) + 1) * (1 - x)) +
        x ^ (i + 1) * (0 + ((i : ℝ) + 1) * (0 - 1))) x := by
    have hp := hasDerivAt_pow (i + 1) x
    simp only [Nat.add_sub_cancel] at hp
    exact hp.mul ((hasDerivAt_const x (1 : ℝ)).add
      (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul ((i : ℝ) + 1)))
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
    have := hasDerivAt_inv hx0.ne'
    simpa [one_div] using this
  have hDd := hinv.sub (((hasDerivAt_const x (1 : ℝ)).sub hw).const_mul s)
  have hlog := (hDd.log hD.ne').div_const (((i : ℝ) + 1) * ((i : ℝ) + 2))
  refine hlog.congr_deriv ?_
  have hA : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  simp only [Pi.sub_apply]
  push_cast
  rw [div_div]
  congr 1
  · ring
  · ring

theorem solution (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (aB9 s)
        ((∑' i : ℕ, (-1 / p ^ 2 + (i + 1) * (i + 2) * s * (p ^ i - p ^ (i + 1))) /
            ((i + 1) * (i + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + (i + 1) * (1 - p)))))) +
          2 * s * (1 - p)) p ∧
      HasDerivAt (aB9 s) (2 * s * (1 - p) - bB9 s p + cB9 s p) p := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hp0, hp1⟩ := hp
  set q : ℝ := p / 2 with hq
  set r : ℝ := (1 + p) / 2 with hr
  have hq0 : 0 < q := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by positivity
  have hpt : p ∈ Set.Ioo q r := ⟨by rw [hq]; linarith, by rw [hr]; linarith⟩
  have h1s : 0 < 1 - s := by linarith
  -- summable bound on the derivatives
  set u : ℕ → ℝ := fun i => 1 / q ^ 2 / (1 - s) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) +
    r ^ i / (1 - s) with hu
  have husum : Summable u :=
    (da_summable_inv.mul_left _).add ((summable_geometric_of_lt_one hr0.le hr1).div_const _)
  have hbound : ∀ (i : ℕ) (y : ℝ), y ∈ Set.Ioo q r →
      ‖(-1 / y ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (y ^ i - y ^ (i + 1))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / y - s * (1 - y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y)))))‖
        ≤ u i := by
    intro i y hy
    have hy0 : 0 < y := lt_trans hq0 hy.1
    have hy1 : y < 1 := lt_trans hy.2 hr1
    obtain ⟨hD1, _⟩ := da_D_bounds hs0 hy0 hy1.le i
    have h1y : 1 ≤ 1 / y := by rw [le_div_iff₀ hy0]; linarith
    have hDge : 1 - s ≤ 1 / y - s * (1 - y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y))) := by linarith
    have hA : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    set D := 1 / y - s * (1 - y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y))) with hDdef
    have hDpos : 0 < D := by linarith
    -- numerator bound
    have hyi : 0 ≤ y ^ i - y ^ (i + 1) := by
      have : y ^ (i + 1) ≤ y ^ i := pow_le_pow_of_le_one hy0.le hy1.le (Nat.le_succ i)
      linarith
    have hyi2 : y ^ i - y ^ (i + 1) ≤ r ^ i := by
      have : y ^ i ≤ r ^ i := pow_le_pow_left₀ hy0.le hy.2.le i
      have : 0 ≤ y ^ (i + 1) := by positivity
      linarith
    have hy2 : 1 / y ^ 2 ≤ 1 / q ^ 2 := one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hq0.le hy.1.le 2)
    have hnum : |-1 / y ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (y ^ i - y ^ (i + 1))| ≤
        1 / q ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * r ^ i := by
      have hpos1 : 0 ≤ 1 / y ^ 2 := by positivity
      have hpos2 : 0 ≤ ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (y ^ i - y ^ (i + 1)) := by positivity
      have hle2 : ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (y ^ i - y ^ (i + 1)) ≤
          ((i : ℝ) + 1) * ((i : ℝ) + 2) * r ^ i := by
        have : s * (y ^ i - y ^ (i + 1)) ≤ r ^ i := by nlinarith
        nlinarith
      rw [abs_le]
      constructor
      · have : -1 / y ^ 2 = -(1 / y ^ 2) := by ring
        rw [this]; nlinarith
      · have : -1 / y ^ 2 = -(1 / y ^ 2) := by ring
        rw [this]; nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hA hDpos)]
    rw [div_le_iff₀ (mul_pos hA hDpos)]
    refine le_trans hnum ?_
    have hu_eq : u i * (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 - s)) =
        1 / q ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * r ^ i := by
      simp only [hu]; field_simp
    have hu0 : 0 ≤ u i := by simp only [hu]; positivity
    have : u i * (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 - s)) ≤ u i * (((i : ℝ) + 1) * ((i : ℝ) + 2) * D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDge hA.le) hu0
    linarith
  -- summability of the terms at `p`
  have hg0 : Summable (fun i : ℕ => Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
    set M : ℝ := Real.log (1 / p) - Real.log (1 - s)
    refine Summable.of_norm_bounded (da_summable_inv.mul_left M) (fun i => ?_)
    obtain ⟨h1, h2⟩ := da_D_bounds hs0 hp0 hp1.le i
    have h1p : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    have hA : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hA, div_le_iff₀ hA]
    have hl1 : Real.log (1 - s) ≤ Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) :=
      Real.log_le_log h1s (by linarith)
    have hl2 : Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) ≤ Real.log (1 / p) :=
      Real.log_le_log (by linarith) h2
    have hlq : 0 ≤ Real.log (1 / p) := Real.log_nonneg h1p
    have hls : Real.log (1 - s) ≤ 0 := Real.log_nonpos h1s.le (by linarith)
    have : M * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) * (((i : ℝ) + 1) * ((i : ℝ) + 2)) = M := by
      field_simp
    rw [this, abs_le]
    constructor <;> linarith
  have hser := hasDerivAt_tsum_of_isPreconnected husum isOpen_Ioo isPreconnected_Ioo
    (g := fun (i : ℕ) (y : ℝ) => Real.log (1 / y - s * (1 - y ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - y)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2)))
    (fun i y hy => da_term_deriv s hs0 hs1 i y (lt_trans hq0 hy.1) (lt_trans hy.2 hr1).le)
    hbound hpt hg0 hpt
  have hpoly : HasDerivAt (fun x : ℝ => s * (2 * x - x ^ 2)) (2 * s * (1 - p)) p := by
    have := ((hasDerivAt_id p).const_mul 2 |>.sub (hasDerivAt_pow 2 p)).const_mul s
    refine this.congr_deriv ?_
    norm_num
    ring
  have hfirst := hser.add hpoly
  have haeq : aB9 s = fun z => (∑' i : ℕ,
      Real.log (1 / z - s * (1 - z ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - z)))) /
        (((i : ℝ) + 1) * ((i : ℝ) + 2))) + s * (2 * z - z ^ 2) := by
    funext z; rfl
  have part1 : HasDerivAt (aB9 s)
        ((∑' i : ℕ, (-1 / p ^ 2 + (i + 1) * (i + 2) * s * (p ^ i - p ^ (i + 1))) /
            ((i + 1) * (i + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + (i + 1) * (1 - p)))))) +
          2 * s * (1 - p)) p := by
    rw [haeq]; exact hfirst
  refine ⟨part1, part1.congr_deriv ?_⟩
  -- identify the series with `-b + c`
  set B : ℕ → ℝ := fun i => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) *
      (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))))) with hB
  set C : ℕ → ℝ := fun i => (p ^ i - p ^ (i + 1)) /
      (1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) with hC
  have hBs : Summable B := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (da_summable_inv.mul_left (1 / (1 - s)))
    · have h1 := (da_D_bounds hs0 hp0 hp1.le i).1
      have : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
      have : 0 < 1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) := by linarith
      simp only [hB]; positivity
    · have h1 := (da_D_bounds hs0 hp0 hp1.le i).1
      have : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
      have hA : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
      simp only [hB]
      rw [show 1 / (1 - s) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) =
        1 / (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 - s)) by field_simp]
      apply one_div_le_one_div_of_le (by positivity)
      apply mul_le_mul_of_nonneg_left (by linarith) hA.le
  have hX : 0 < 1 / (p * s) - 1 := by
    have : 1 < 1 / (p * s) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hCs : Summable C := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      ((summable_geometric_of_lt_one hp0.le hp1).div_const (1 / (p * s) - 1))
    · have h1 : 0 ≤ p ^ i - p ^ (i + 1) := by
        have : p ^ (i + 1) ≤ p ^ i := pow_le_pow_of_le_one hp0.le hp1.le (Nat.le_succ i)
        linarith
      have h2 := (da_w_bounds hp0 hp1.le i).1
      simp only [hC]
      have : 0 < 1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) := by linarith
      positivity
    · have h1 : 0 ≤ p ^ i - p ^ (i + 1) := by
        have : p ^ (i + 1) ≤ p ^ i := pow_le_pow_of_le_one hp0.le hp1.le (Nat.le_succ i)
        linarith
      have h2 := (da_w_bounds hp0 hp1.le i).1
      simp only [hC]
      have h3 : p ^ i - p ^ (i + 1) ≤ p ^ i := by have : 0 ≤ p ^ (i + 1) := by positivity
                                                  linarith
      calc (p ^ i - p ^ (i + 1)) / (1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))
          ≤ (p ^ i - p ^ (i + 1)) / (1 / (p * s) - 1) :=
            div_le_div_of_nonneg_left h1 hX (by linarith)
        _ ≤ p ^ i / (1 / (p * s) - 1) := div_le_div_of_nonneg_right h3 hX.le
  have hterm : ∀ i : ℕ, (-1 / p ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (p ^ i - p ^ (i + 1))) /
      (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))))) =
      (-(1 / p ^ 2)) * B i + C i := by
    intro i
    have h1 := (da_D_bounds hs0 hp0 hp1.le i).1
    have : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    have hDp : 0 < 1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p))) := by linarith
    have hE : 1 / (p * s) - 1 + p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)) =
        (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))) / s := by
      field_simp
      ring
    have hA : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    simp only [hB, hC]
    rw [hE]
    field_simp
  have hsum : (∑' i : ℕ, (-1 / p ^ 2 + ((i : ℝ) + 1) * ((i : ℝ) + 2) * s * (p ^ i - p ^ (i + 1))) /
      (((i : ℝ) + 1) * ((i : ℝ) + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + ((i : ℝ) + 1) * (1 - p)))))) =
      -bB9 s p + cB9 s p := by
    rw [tsum_congr hterm, (hBs.mul_left _).tsum_add hCs, tsum_mul_left]
    unfold bB9 cB9
    simp only [hB, hC]
    ring
  push_cast at hsum ⊢
  rw [hsum]
  ring
