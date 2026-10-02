-- Prove2me | solution 1 for Transcendence.siegel_small_values_parameters
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:49:42.987346+00:00
-- url     : https://prove2.me/submissions/c81bb3b4-ca34-48d3-8fc5-4ab6fe0089de

import Mathlib

/-!
# The parameters of Proposition 4.10 (Waldschmidt, DALAG §4.5)

With `W = N + U + V`, take `T = ⌈(4/3) W / log(R/r)⌉`, `X = ⌊e^N⌋` and `ℓ = ⌈(8/3) Tⁿ e^W⌉`. The
book's inequality `3((4/3)W + 1)ⁿ < e^{W/3}` for `W ≥ 12n²` (`num_bound`, tight at `n = 1`,
`W = 12`) gives `ℓ ≤ e^{4W/3}`, and `T log(R/r) < (3/2) W` with the main hypothesis gives
`(8/3) W Tⁿ ≤ L N`, hence the count `ℓ^{2Tⁿ} < (X + 1)^L`. The value bounds are
`Tⁿ · 2 e^U X / ℓ ≤ (3/4) e^{-V}` and, as `r/R ≤ 1/e ≤ 1/2` and `(r/R)^T ≤ e^{-4W/3}`,
`X e^U (r/R)^T / (1 - r/R) ≤ 2 e^{N+U} e^{-4W/3} ≤ (1/4) e^{-V}`.
-/

namespace SiegelSmallValuesParameters

lemma exp_four_gt : (54 : ℝ) < Real.exp 4 := by
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h4 : Real.exp 4 = (Real.exp 1 ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : (7.38 : ℝ) < Real.exp 1 ^ 2 := by nlinarith
  rw [h4]; nlinarith

/-- `3 (y² + 1) < e^y` for `y ≥ 4` (tight at `y = 4`: `51 < 54.6`). -/
lemma three_mul_lt_exp {y : ℝ} (hy : 4 ≤ y) : 3 * (y ^ 2 + 1) < Real.exp y := by
  set t := y - 4 with ht
  have ht0 : 0 ≤ t := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg ht0
  have he4 := exp_four_gt
  have hexp : Real.exp y = Real.exp 4 * Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have hy' : y = t + 4 := by ring
  rw [hexp, hy']
  nlinarith [mul_le_mul_of_nonneg_left hq (Real.exp_pos 4).le,
    mul_lt_mul_of_pos_right he4 (by positivity : (0 : ℝ) < 1 + t + t ^ 2 / 2)]

/-- The book's `3((4/3)W + 1)ⁿ < e^{W/3}` for `W ≥ 12n²`. -/
lemma num_bound {n : ℕ} (hn : 0 < n) {W : ℝ} (hW : 12 * (n : ℝ) ^ 2 ≤ W) {T : ℕ}
    (hT : (T : ℝ) ≤ 4 / 3 * W + 1) : 3 * (T : ℝ) ^ n < Real.exp (W / 3) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3n : (0 : ℝ) < 3 * n := by positivity
  set y := W / (3 * n) with hy
  have hW' : W = 3 * n * y := by rw [hy]; field_simp
  have hy4n : 4 * (n : ℝ) ≤ y := by
    rw [hy, le_div_iff₀ h3n]; nlinarith
  have hy4 : (4 : ℝ) ≤ y := by nlinarith
  have hTy : (T : ℝ) ≤ y ^ 2 + 1 := by
    have h1 : 4 / 3 * W = 4 * n * y := by rw [hW']; ring
    have h2 : 4 * (n : ℝ) * y ≤ y * y := mul_le_mul_of_nonneg_right hy4n (by linarith)
    nlinarith
  have hexp : Real.exp (W / 3) = Real.exp y ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hW']; field_simp
  rw [hexp]
  calc 3 * (T : ℝ) ^ n ≤ 3 * (y ^ 2 + 1) ^ n := by
        gcongr
    _ ≤ 3 ^ n * (y ^ 2 + 1) ^ n := by
        gcongr; exact le_self_pow₀ (by norm_num) hn.ne'
    _ = (3 * (y ^ 2 + 1)) ^ n := by rw [mul_pow]
    _ < Real.exp y ^ n := pow_lt_pow_left₀ (three_mul_lt_exp hy4) (by positivity) hn.ne'

lemma pow_bound {n : ℕ} (hn : 0 < n) : (3 / 2 : ℝ) ^ n * (8 / 3) ≤ 2 ^ (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2) m
  calc (3 / 2 : ℝ) ^ (m + 1) * (8 / 3) = 4 * (3 / 2) ^ m := by ring
    _ ≤ 4 * 2 ^ m := by linarith
    _ = 2 ^ (m + 1 + 1) := by ring

end SiegelSmallValuesParameters

theorem solution {n L : ℕ} (hn : 0 < n) {N U V r R : ℝ} (hr : 0 < r)
    (hW : 12 * (n : ℝ) ^ 2 ≤ N + U + V)
    (hRe : Real.exp 1 * r ≤ R) (hRW : R ≤ r * Real.exp ((N + U + V) / 6))
    (hmain : (2 * (N + U + V)) ^ (n + 1) ≤ L * N * Real.log (R / r) ^ n) :
    ∃ T X ℓ : ℕ, 0 < ℓ ∧ (X : ℝ) ≤ Real.exp N ∧ ℓ ^ (2 * T ^ n) < (X + 1) ^ L ∧
      (T : ℝ) ^ n * (2 * (Real.exp U * X / ℓ)) ≤ 3 / 4 * Real.exp (-V) ∧
      X * Real.exp U * (r / R) ^ T / (1 - r / R) ≤ 1 / 4 * Real.exp (-V) := by
  set W := N + U + V with hWdef
  set ℓ₀ := Real.log (R / r) with hℓ₀
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hW12 : (12 : ℝ) ≤ W := by nlinarith
  have hW0 : 0 < W := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR : 0 < R := lt_of_lt_of_le (mul_pos (Real.exp_pos 1) hr) hRe
  have h2rR : 2 * r ≤ R := by nlinarith
  have hRr : Real.exp 1 ≤ R / r := by rw [le_div_iff₀ hr]; exact hRe
  have hℓ₀1 : 1 ≤ ℓ₀ := by
    rw [hℓ₀, Real.le_log_iff_exp_le (div_pos hR hr)]; exact hRr
  have hℓ₀W : ℓ₀ ≤ W / 6 := by
    rw [hℓ₀, Real.log_le_iff_le_exp (div_pos hR hr), div_le_iff₀ hr]
    linarith [hRW]
  have hℓ₀pos : 0 < ℓ₀ := by linarith
  -- the order `T` of the Taylor polynomial: `(4/3) W ≤ T log(R/r) < (4/3) W + log(R/r)`
  set T := ⌈4 / 3 * W / ℓ₀⌉₊ with hTdef
  have hTge : 4 / 3 * W / ℓ₀ ≤ T := Nat.le_ceil _
  have hTlt : (T : ℝ) < 4 / 3 * W / ℓ₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hTlow : 4 / 3 * W ≤ T * ℓ₀ := by rwa [div_le_iff₀ hℓ₀pos] at hTge
  have hThigh : (T : ℝ) * ℓ₀ ≤ 3 / 2 * W := by
    have h1 : (T : ℝ) * ℓ₀ < (4 / 3 * W / ℓ₀ + 1) * ℓ₀ := mul_lt_mul_of_pos_right hTlt hℓ₀pos
    have h2 : (4 / 3 * W / ℓ₀ + 1) * ℓ₀ = 4 / 3 * W + ℓ₀ := by field_simp
    linarith
  have hTW : (T : ℝ) ≤ 4 / 3 * W + 1 := by
    have : 4 / 3 * W / ℓ₀ ≤ 4 / 3 * W := div_le_self (by positivity) hℓ₀1
    linarith
  have hT3 : 3 * (T : ℝ) ^ n < Real.exp (W / 3) := SiegelSmallValuesParameters.num_bound hn hW hTW
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hTge
  have hTn : (0 : ℝ) < (T : ℝ) ^ n := by positivity
  -- the height `X = ⌊e^N⌋` and the number `ℓ` of cells
  set X := ⌊Real.exp N⌋₊ with hXdef
  have hXle : (X : ℝ) ≤ Real.exp N := Nat.floor_le (Real.exp_pos N).le
  have hXlt : Real.exp N < X + 1 := Nat.lt_floor_add_one _
  set ℓ := ⌈8 / 3 * (T : ℝ) ^ n * Real.exp W⌉₊ with hℓdef
  have hℓge : 8 / 3 * (T : ℝ) ^ n * Real.exp W ≤ ℓ := Nat.le_ceil _
  have hℓlt : (ℓ : ℝ) < 8 / 3 * (T : ℝ) ^ n * Real.exp W + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hℓpos' : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓge
  have hℓpos : 0 < ℓ := by exact_mod_cast hℓpos'
  have hℓexp : (ℓ : ℝ) ≤ Real.exp (4 / 3 * W) := by
    have e1 : Real.exp (4 / 3 * W) = Real.exp (W / 3) * Real.exp W := by
      rw [← Real.exp_add]; ring_nf
    have e2 : (9 : ℝ) ≤ Real.exp (4 / 3 * W) := by
      have := Real.add_one_le_exp (4 / 3 * W); linarith
    have e3 : 8 / 3 * (T : ℝ) ^ n * Real.exp W ≤ 8 / 9 * Real.exp (4 / 3 * W) := by
      rw [e1]; nlinarith [mul_lt_mul_of_pos_right hT3 (Real.exp_pos W)]
    linarith
  -- the count `ℓ^{2Tⁿ} < (X+1)^L`
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · exfalso
      rw [h] at hmain
      simp only [Nat.cast_zero, zero_mul] at hmain
      have : 0 < (2 * W) ^ (n + 1) := by positivity
      linarith
    · exact h
  have hkey : 8 / 3 * W * (T : ℝ) ^ n ≤ L * N := by
    have h2 : (3 / 2 : ℝ) ^ n * (8 / 3) ≤ 2 ^ (n + 1) := SiegelSmallValuesParameters.pow_bound hn
    have hℓn : 0 < ℓ₀ ^ n := by positivity
    have h3 : 8 / 3 * W * (T : ℝ) ^ n * ℓ₀ ^ n ≤ (2 * W) ^ (n + 1) := by
      calc 8 / 3 * W * (T : ℝ) ^ n * ℓ₀ ^ n = 8 / 3 * W * ((T : ℝ) * ℓ₀) ^ n := by ring
        _ ≤ 8 / 3 * W * (3 / 2 * W) ^ n := by gcongr
        _ = ((3 / 2 : ℝ) ^ n * (8 / 3)) * W ^ (n + 1) := by
            have hpow : ∀ (a : ℝ) (m : ℕ),
                8 / 3 * a * (3 / 2 * a) ^ m = ((3 / 2 : ℝ) ^ m * (8 / 3)) * a ^ (m + 1) := by
              intro a m; ring
            exact hpow W n
        _ ≤ 2 ^ (n + 1) * W ^ (n + 1) := by gcongr
        _ = (2 * W) ^ (n + 1) := by rw [mul_pow]
    have h4 : 8 / 3 * W * (T : ℝ) ^ n * ℓ₀ ^ n ≤ L * N * ℓ₀ ^ n := le_trans h3 hmain
    exact le_of_mul_le_mul_right h4 hℓn
  have hcount : ℓ ^ (2 * T ^ n) < (X + 1) ^ L := by
    have h : (ℓ : ℝ) ^ (2 * T ^ n) < ((X : ℝ) + 1) ^ L := by
      calc (ℓ : ℝ) ^ (2 * T ^ n) ≤ Real.exp (4 / 3 * W) ^ (2 * T ^ n) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hℓexp _
        _ = Real.exp (8 / 3 * W * (T : ℝ) ^ n) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ Real.exp (L * N) := Real.exp_le_exp.mpr hkey
        _ = Real.exp N ^ L := by rw [← Real.exp_nat_mul]
        _ < ((X : ℝ) + 1) ^ L := pow_lt_pow_left₀ hXlt (Real.exp_pos N).le hL0.ne'
    exact_mod_cast h
  refine ⟨T, X, ℓ, hℓpos, hXle, hcount, ?_, ?_⟩
  · -- the Taylor polynomial: `Tⁿ · 2 e^U X / ℓ ≤ (3/4) e^{-V}`
    have hEW : Real.exp U * Real.exp N = Real.exp (-V) * Real.exp W := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hWdef]; ring
    rw [show (T : ℝ) ^ n * (2 * (Real.exp U * X / ℓ)) = (T : ℝ) ^ n * (2 * (Real.exp U * X)) / ℓ
      by ring, div_le_iff₀ hℓpos']
    calc (T : ℝ) ^ n * (2 * (Real.exp U * X)) ≤ (T : ℝ) ^ n * (2 * (Real.exp U * Real.exp N)) := by
          gcongr
      _ = 3 / 4 * Real.exp (-V) * (8 / 3 * (T : ℝ) ^ n * Real.exp W) := by rw [hEW]; ring
      _ ≤ 3 / 4 * Real.exp (-V) * ℓ := by gcongr
  · -- the tail: `X e^U (r/R)^T / (1 - r/R) ≤ (1/4) e^{-V}`
    set q := r / R with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hq2 : q ≤ 1 / 2 := by
      rw [hqdef, div_le_iff₀ hR]; linarith
    have hqT : q ^ T ≤ Real.exp (-(4 / 3 * W)) := by
      have hq : q = Real.exp (-ℓ₀) := by
        rw [Real.exp_neg, hℓ₀, Real.exp_log (div_pos hR hr), inv_div]
      rw [hq, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      linarith
    have h1 : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : Real.exp N * Real.exp U * Real.exp (-(4 / 3 * W)) =
        Real.exp (-V) * Real.exp (-(W / 3)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hWdef]; ring
    have h3 : Real.exp (-(W / 3)) ≤ 1 / 8 := by
      have h8 : (8 : ℝ) ≤ Real.exp (W / 3) := by
        have h54 := SiegelSmallValuesParameters.exp_four_gt
        have h4 : Real.exp 4 ≤ Real.exp (W / 3) := Real.exp_le_exp.mpr (by linarith)
        linarith
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    rw [div_eq_mul_inv]
    calc (X : ℝ) * Real.exp U * q ^ T * (1 - q)⁻¹
        ≤ Real.exp N * Real.exp U * Real.exp (-(4 / 3 * W)) * 2 := by
          refine mul_le_mul ?_ h1 (inv_nonneg.mpr (by linarith)) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hXle (Real.exp_pos U).le) hqT
            (pow_nonneg hq0 T) (by positivity)
      _ = Real.exp (-V) * Real.exp (-(W / 3)) * 2 := by rw [h2]
      _ ≤ Real.exp (-V) * (1 / 8) * 2 := by gcongr
      _ = 1 / 4 * Real.exp (-V) := by ring
