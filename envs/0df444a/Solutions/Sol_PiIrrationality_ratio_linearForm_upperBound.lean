-- Prove2me | solution 1 for PiIrrationality.ratio_linearForm_upperBound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T09:29:32.53922+00:00
-- url     : https://prove2.me/submissions/b14894fb-7ca4-414f-bc95-721cdbe18e55

import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Irrational

open Filter Real

namespace PiIrrationality.RatioCriterion

/-- The integer attached to a rational approximation: `qΛ = A + V Δ`. -/
lemma key_identity (U V p : ℤ) (q : ℕ) :
    (q : ℝ) * ((U : ℝ) + V * π) = ((q * U + p * V : ℤ) : ℝ) + V * (q * π - p) := by
  push_cast; ring

/-- If the paired integer is nonzero and `q |Λ| < 1/2`, then `|V| |Δ| > 1/2`. -/
lemma half_lt_of_ne (U V p : ℤ) (q : ℕ) (hA : (q : ℤ) * U + p * V ≠ 0)
    (hsmall : (q : ℝ) * |(U : ℝ) + V * π| < 1 / 2) :
    1 / 2 < |(V : ℝ)| * |(q : ℝ) * π - p| := by
  have hA1 : (1 : ℝ) ≤ |((q * U + p * V : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |(q : ℤ) * U + p * V| := Int.one_le_abs hA
    exact_mod_cast this
  have hid := key_identity U V p q
  have heq : ((q * U + p * V : ℤ) : ℝ) = (q : ℝ) * ((U : ℝ) + V * π) -
      (V : ℝ) * ((q : ℝ) * π - p) := by rw [hid]; ring
  have h1 := abs_sub ((q : ℝ) * ((U : ℝ) + V * π)) ((V : ℝ) * ((q : ℝ) * π - p))
  rw [← heq, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q)] at h1
  linarith

/-- If the paired integer vanishes, `|V| |Δ| = q |Λ|`. -/
lemma delta_eq_of_eq_zero (U V p : ℤ) (q : ℕ) (hA : (q : ℤ) * U + p * V = 0) :
    |(V : ℝ)| * |(q : ℝ) * π - p| = (q : ℝ) * |(U : ℝ) + V * π| := by
  have hid := key_identity U V p q
  rw [hA] at hid
  simp only [Int.cast_zero, zero_add] at hid
  rw [← abs_mul, ← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q)]

/-- The core estimate: `|qπ - p| ≥ c q^{-κ}` for all large `q`. -/
theorem core (U V : ℕ → ℤ) (s t g : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hsg : s < g) (n₀ : ℕ)
    (hV : ∀ n, n₀ ≤ n → V n ≠ 0 ∧ |(V n : ℝ)| ≤ Real.exp (s * n))
    (hΛ : ∀ n, n₀ ≤ n → |(U n : ℝ) + V n * π| ≤ Real.exp (-(t * n)))
    (hratio : ∀ n, n₀ ≤ n →
      |(U n : ℝ) + V n * π| ≤ Real.exp (-(g * n)) * |(V n : ℝ)|) :
    ∃ c > 0, ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      c * (q : ℝ) ^ (-(max (s / t) (s / (g - s)))) ≤ |(q : ℝ) * π - p| := by
  set κ := max (s / t) (s / (g - s)) with hκ
  have hgs : 0 < g - s := by linarith
  have hg : 0 < g := by linarith
  set r := s / g with hr
  have hr0 : 0 < r := div_pos hs hg
  have hr1 : r < 1 := (div_lt_one hg).mpr hsg
  set c₁ : ℝ := 1 / (2 * Real.exp s * 2 ^ (s / t)) with hc₁
  set c₂ : ℝ := (Real.exp (-s) / 2) ^ (1 / (1 - r)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨min c₁ c₂, lt_min hc₁0 hc₂0, ⌈Real.exp (t * n₀)⌉₊ + 1, ?_⟩
  intro p q hq
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := le_trans (Nat.le_add_left 1 _) hq
    exact_mod_cast this
  have hq0 : (0 : ℝ) < q := by linarith
  have hqbig : Real.exp (t * n₀) < 2 * q := by
    have h1 : Real.exp (t * n₀) ≤ ⌈Real.exp (t * n₀)⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp (t * n₀)⌉₊ + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hq
    push_cast at h2
    linarith
  -- Δ ≠ 0 by irrationality of π
  set Δ : ℝ := (q : ℝ) * π - p with hΔ
  have hΔ0 : Δ ≠ 0 := by
    have hqne : q ≠ 0 := by
      intro h; rw [h] at hq1; norm_num at hq1
    exact ((irrational_pi.natCast_mul hqne).sub_intCast p).ne_zero
  have hΔpos : 0 < |Δ| := abs_pos.mpr hΔ0
  -- the scale index
  have hex : ∃ n : ℕ, 2 * (q : ℝ) < Real.exp (t * n) := by
    obtain ⟨n, hn⟩ := (tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop ht)).eventually_gt_atTop
      (2 * (q : ℝ)) |>.exists
    exact ⟨n, hn⟩
  classical
  set N := Nat.find hex with hN
  have hNspec : 2 * (q : ℝ) < Real.exp (t * N) := Nat.find_spec hex
  have hN0 : n₀ < N := by
    by_contra h
    push Not at h
    have : Real.exp (t * N) ≤ Real.exp (t * n₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast h) ht.le)
    linarith
  have hNprev : Real.exp (t * (N - 1 : ℕ)) ≤ 2 * q := by
    have := Nat.find_min hex (show N - 1 < N by omega)
    push Not at this
    exact this
  -- smallness at every index ≥ N
  have hsmall : ∀ n, N ≤ n → (q : ℝ) * |(U n : ℝ) + V n * π| < 1 / 2 := by
    intro n hn
    have h1 := hΛ n (by omega)
    have h2 : Real.exp (t * N) ≤ Real.exp (t * n) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) ht.le)
    have h3 : (q : ℝ) * |(U n : ℝ) + V n * π| ≤ q * Real.exp (-(t * n)) :=
      mul_le_mul_of_nonneg_left h1 hq0.le
    have h4 : (q : ℝ) * Real.exp (-(t * n)) < 1 / 2 := by
      rw [Real.exp_neg]
      have he := Real.exp_pos (t * n)
      rw [← div_eq_mul_inv, div_lt_iff₀ he]
      linarith
    linarith
  -- lower bound at any index ≥ N with nonzero paired integer
  have hlow : ∀ n, N ≤ n → (q : ℤ) * U n + p * V n ≠ 0 →
      Real.exp (-(s * n)) / 2 < |Δ| := by
    intro n hn hA
    have h1 := half_lt_of_ne (U n) (V n) p q hA (hsmall n hn)
    have h2 := (hV n (by omega)).2
    have hVpos : 0 < |(V n : ℝ)| := abs_pos.mpr (by exact_mod_cast (hV n (by omega)).1)
    have h3 : 1 / 2 < Real.exp (s * n) * |Δ| :=
      lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    calc Real.exp (-(s * n)) / 2 = Real.exp (-(s * n)) * (1 / 2) := by ring
      _ < Real.exp (-(s * n)) * (Real.exp (s * n) * |Δ|) :=
          mul_lt_mul_of_pos_left h3 (Real.exp_pos _)
      _ = |Δ| := by rw [← mul_assoc, ← Real.exp_add]; simp
  have hqκ : ∀ x : ℝ, x ≤ κ → (q : ℝ) ^ (-κ) ≤ (q : ℝ) ^ (-x) := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  by_cases hAN : (q : ℤ) * U N + p * V N ≠ 0
  · -- Case 1
    have h1 := hlow N le_rfl hAN
    -- exp(-sN) ≥ exp(-s) (2q)^{-s/t}
    have h2 : Real.exp (-s) * (2 * (q : ℝ)) ^ (-(s / t)) ≤ Real.exp (-(s * N)) := by
      have hlog : Real.exp (t * (N - 1 : ℕ)) ≤ 2 * q := hNprev
      have hpow : (2 * (q : ℝ)) ^ (-(s / t)) ≤ Real.exp (t * (N - 1 : ℕ)) ^ (-(s / t)) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hlog (by
          have := div_pos hs ht; linarith)
      rw [← Real.exp_mul] at hpow
      have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hN1] at hpow
      have : t * ((N : ℝ) - 1) * -(s / t) = -(s * N) + s := by field_simp; ring
      rw [this, Real.exp_add] at hpow
      calc Real.exp (-s) * (2 * (q : ℝ)) ^ (-(s / t))
          ≤ Real.exp (-s) * (Real.exp (-(s * N)) * Real.exp s) :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
        _ = Real.exp (-(s * N)) := by
            rw [mul_comm, mul_assoc, ← Real.exp_add]; simp
    have h3 : (2 * (q : ℝ)) ^ (-(s / t)) = 2 ^ (-(s / t)) * (q : ℝ) ^ (-(s / t)) :=
      Real.mul_rpow (by norm_num) hq0.le
    have h4 : c₁ * (q : ℝ) ^ (-(s / t)) = Real.exp (-s) * (2 * (q : ℝ)) ^ (-(s / t)) / 2 := by
      rw [h3, hc₁, Real.exp_neg, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    calc min c₁ c₂ * (q : ℝ) ^ (-κ) ≤ c₁ * (q : ℝ) ^ (-(s / t)) :=
          mul_le_mul (min_le_left _ _) (hqκ _ (le_max_left _ _)) (by positivity) hc₁0.le
      _ = Real.exp (-s) * (2 * (q : ℝ)) ^ (-(s / t)) / 2 := h4
      _ ≤ Real.exp (-(s * N)) / 2 := by linarith
      _ ≤ |Δ| := h1.le
  · -- Case 2
    push Not at hAN
    have hexM : ∃ m, N ≤ m ∧ (q : ℤ) * U m + p * V m ≠ 0 := by
      by_contra hcon
      push Not at hcon
      -- then |Δ| ≤ q exp(-g m) for all m ≥ N, forcing Δ = 0
      have hb : ∀ m, N ≤ m → |Δ| ≤ q * Real.exp (-(g * m)) := by
        intro m hm
        have h1 := delta_eq_of_eq_zero (U m) (V m) p q (hcon m hm)
        have h2 := hratio m (by omega)
        have hVpos : 0 < |(V m : ℝ)| := abs_pos.mpr (by exact_mod_cast (hV m (by omega)).1)
        have h3 : |(V m : ℝ)| * |Δ| ≤ |(V m : ℝ)| * (q * Real.exp (-(g * m))) := by
          rw [h1]
          calc (q : ℝ) * |(U m : ℝ) + V m * π| ≤ q * (Real.exp (-(g * m)) * |(V m : ℝ)|) :=
                mul_le_mul_of_nonneg_left h2 hq0.le
            _ = |(V m : ℝ)| * (q * Real.exp (-(g * m))) := by ring
        exact le_of_mul_le_mul_left h3 hVpos
      have hlim : Tendsto (fun m : ℕ => (q : ℝ) * Real.exp (-(g * m))) atTop (nhds 0) := by
        have : Tendsto (fun m : ℕ => Real.exp (-(g * m))) atTop (nhds 0) := by
          apply Real.tendsto_exp_atBot.comp
          exact tendsto_neg_atTop_atBot.comp
            ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hg)
        simpa using this.const_mul (q : ℝ)
      have hev := (hlim.eventually (gt_mem_nhds hΔpos))
      obtain ⟨m, hm⟩ := (hev.and (eventually_ge_atTop N)).exists
      linarith [hb m hm.2, hm.1]
    set M := Nat.find hexM with hM
    obtain ⟨hNM, hAM⟩ := Nat.find_spec hexM
    have hMN : N < M := by
      rcases lt_or_eq_of_le hNM with h | h
      · exact h
      · exfalso; rw [← h] at hAM; exact hAM hAN
    have hAM1 : (q : ℤ) * U (M - 1) + p * V (M - 1) = 0 := by
      have := Nat.find_min hexM (show M - 1 < M by omega)
      push Not at this
      exact this (by omega)
    -- upper bound for |Δ| at M - 1
    have hup : |Δ| ≤ q * Real.exp (-(g * (M - 1 : ℕ))) := by
      have h1 := delta_eq_of_eq_zero (U (M - 1)) (V (M - 1)) p q hAM1
      have h2 := hratio (M - 1) (by omega)
      have hVpos : 0 < |(V (M - 1) : ℝ)| :=
        abs_pos.mpr (by exact_mod_cast (hV (M - 1) (by omega)).1)
      have h3 : |(V (M - 1) : ℝ)| * |Δ| ≤
          |(V (M - 1) : ℝ)| * (q * Real.exp (-(g * (M - 1 : ℕ)))) := by
        rw [h1]
        calc (q : ℝ) * |(U (M - 1) : ℝ) + V (M - 1) * π|
            ≤ q * (Real.exp (-(g * (M - 1 : ℕ))) * |(V (M - 1) : ℝ)|) :=
              mul_le_mul_of_nonneg_left h2 hq0.le
          _ = |(V (M - 1) : ℝ)| * (q * Real.exp (-(g * (M - 1 : ℕ)))) := by ring
      exact le_of_mul_le_mul_left h3 hVpos
    have hlowM := hlow M hNM hAM
    -- exp(g (M-1)) ≤ q / |Δ|
    have hE : Real.exp (g * (M - 1 : ℕ)) ≤ q / |Δ| := by
      rw [le_div_iff₀ hΔpos]
      have := hup
      rw [Real.exp_neg] at this
      have he := Real.exp_pos (g * (M - 1 : ℕ))
      calc Real.exp (g * (M - 1 : ℕ)) * |Δ|
          ≤ Real.exp (g * (M - 1 : ℕ)) * (q * (Real.exp (g * (M - 1 : ℕ)))⁻¹) :=
            mul_le_mul_of_nonneg_left this he.le
        _ = q := by field_simp
    -- exp(s (M-1)) ≤ (q/|Δ|)^r
    have hE2 : Real.exp (s * (M - 1 : ℕ)) ≤ ((q : ℝ) / |Δ|) ^ r := by
      have := Real.rpow_le_rpow (Real.exp_pos _).le hE hr0.le
      rw [← Real.exp_mul] at this
      have heq : g * ((M - 1 : ℕ) : ℝ) * r = s * (M - 1 : ℕ) := by
        rw [hr]; field_simp
      rwa [heq] at this
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    -- exp(-sM) = exp(-s) exp(-s(M-1)) ≥ exp(-s) (|Δ|/q)^r
    have hE3 : Real.exp (-s) * (|Δ| / q) ^ r ≤ Real.exp (-(s * M)) := by
      have h1 : (|Δ| / (q : ℝ)) ^ r = (((q : ℝ) / |Δ|) ^ r)⁻¹ := by
        rw [← Real.inv_rpow (by positivity), inv_div]
      rw [h1]
      have hpos : 0 < Real.exp (s * (M - 1 : ℕ)) := Real.exp_pos _
      have h2 : (((q : ℝ) / |Δ|) ^ r)⁻¹ ≤ (Real.exp (s * (M - 1 : ℕ)))⁻¹ :=
        inv_anti₀ hpos hE2
      rw [hM1, ← Real.exp_neg] at h2
      calc Real.exp (-s) * (((q : ℝ) / |Δ|) ^ r)⁻¹
          ≤ Real.exp (-s) * Real.exp (-(s * ((M : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (-(s * M)) := by rw [← Real.exp_add]; ring_nf
    -- combine: |Δ| > exp(-s)/2 (|Δ|/q)^r
    have hc : Real.exp (-s) / 2 * (|Δ| / q) ^ r < |Δ| := by linarith
    -- |Δ|^(1-r) > (exp(-s)/2) q^(-r)
    have hdiv : (|Δ| / (q : ℝ)) ^ r = |Δ| ^ r * (q : ℝ) ^ (-r) := by
      rw [Real.div_rpow hΔpos.le hq0.le, Real.rpow_neg hq0.le, div_eq_mul_inv]
    rw [hdiv] at hc
    have hΔr : |Δ| = |Δ| ^ r * |Δ| ^ (1 - r) := by
      rw [← Real.rpow_add hΔpos]; simp
    have hc2 : Real.exp (-s) / 2 * (q : ℝ) ^ (-r) < |Δ| ^ (1 - r) := by
      have hpos : 0 < |Δ| ^ r := Real.rpow_pos_of_pos hΔpos r
      have : |Δ| ^ r * (Real.exp (-s) / 2 * (q : ℝ) ^ (-r)) < |Δ| ^ r * |Δ| ^ (1 - r) := by
        rw [← hΔr]; linarith
      exact lt_of_mul_lt_mul_left this hpos.le
    have h1r : 0 < 1 - r := by linarith
    have hc3 : (Real.exp (-s) / 2 * (q : ℝ) ^ (-r)) ^ (1 / (1 - r)) < |Δ| := by
      have := Real.rpow_lt_rpow (by positivity) hc2 (by positivity : 0 < 1 / (1 - r))
      rwa [← Real.rpow_mul hΔpos.le, mul_one_div_cancel h1r.ne', Real.rpow_one] at this
    have hexp : (Real.exp (-s) / 2 * (q : ℝ) ^ (-r)) ^ (1 / (1 - r)) =
        c₂ * (q : ℝ) ^ (-(s / (g - s))) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le]
      congr 2
      rw [hr]; field_simp
    rw [hexp] at hc3
    calc min c₁ c₂ * (q : ℝ) ^ (-κ) ≤ c₂ * (q : ℝ) ^ (-(s / (g - s))) :=
          mul_le_mul (min_le_right _ _) (hqκ _ (le_max_right _ _)) (by positivity) hc₂0.le
      _ ≤ |Δ| := hc3.le

end PiIrrationality.RatioCriterion

open PiIrrationality.RatioCriterion in
theorem solution
    (U V : ℕ → ℤ) (s t g B : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hsg : s < g)
    (hB₁ : 1 + s / t ≤ B) (hB₂ : 1 + s / (g - s) ≤ B)
    (hV : ∀ᶠ n : ℕ in atTop, V n ≠ 0 ∧ |(V n : ℝ)| ≤ Real.exp (s * n))
    (hΛ : ∀ᶠ n : ℕ in atTop, |(U n : ℝ) + V n * Real.pi| ≤ Real.exp (-(t * n)))
    (hratio : ∀ᶠ n : ℕ in atTop,
      |(U n : ℝ) + V n * Real.pi| ≤ Real.exp (-(g * n)) * |(V n : ℝ)|) :
    PiIrrationality.UpperBound B := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ((hV.and hΛ).and hratio)
  obtain ⟨c, hc, Q, hQ⟩ := core U V s t g hs ht hsg n₀ (fun n hn => (hn₀ n hn).1.1)
    (fun n hn => (hn₀ n hn).1.2) (fun n hn => (hn₀ n hn).2)
  set κ := max (s / t) (s / (g - s))
  have hκB : 1 + κ ≤ B := by
    rcases le_total (s / t) (s / (g - s)) with h' | h'
    · simp only [κ, max_eq_right h']; linarith
    · simp only [κ, max_eq_left h']; linarith
  intro ε hε
  -- choose Q' with q^{-ε} < c
  obtain ⟨Q', hQ'⟩ : ∃ Q' : ℕ, ∀ q : ℕ, Q' ≤ q → (q : ℝ) ^ (-ε) < c := by
    have ht : Tendsto (fun q : ℕ => (q : ℝ) ^ (-ε)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
    obtain ⟨Q', hQ'⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
    exact ⟨Q', hQ'⟩
  refine ⟨max (max Q Q') 1, ?_⟩
  intro p q hq hqQ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (le_max_right _ _) hqQ)
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 := hQ p q (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hqQ)
  have h2 := hQ' q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hqQ)
  -- |π - p/q| = |qπ - p| / q
  have hrew : |Real.pi - (p : ℝ) / q| = |(q : ℝ) * Real.pi - p| / q := by
    rw [show Real.pi - (p : ℝ) / q = ((q : ℝ) * Real.pi - p) / q by field_simp,
      abs_div, abs_of_pos hq0]
  rw [hrew, lt_div_iff₀ hq0]
  -- 1/q^{B+ε} * q ≤ q^{-(κ+ε)} < c q^{-κ}
  have h3 : 1 / (q : ℝ) ^ (B + ε) * q ≤ (q : ℝ) ^ (-ε) * (q : ℝ) ^ (-κ) := by
    rw [← Real.rpow_add hq0, one_div, ← Real.rpow_neg hq0.le]
    calc (q : ℝ) ^ (-(B + ε)) * q = (q : ℝ) ^ (-(B + ε) + 1) := by
          rw [Real.rpow_add hq0, Real.rpow_one]
      _ ≤ (q : ℝ) ^ (-ε + -κ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hqκpos : 0 < (q : ℝ) ^ (-κ) := Real.rpow_pos_of_pos hq0 _
  calc 1 / (q : ℝ) ^ (B + ε) * q ≤ (q : ℝ) ^ (-ε) * (q : ℝ) ^ (-κ) := h3
    _ < c * (q : ℝ) ^ (-κ) := mul_lt_mul_of_pos_right h2 hqκpos
    _ ≤ |(q : ℝ) * Real.pi - p| := h1
