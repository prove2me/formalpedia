-- Prove2me | solution 1 for Transcendence.schneider_lang_extrapolation_ineq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:35:00.020727+00:00
-- url     : https://prove2.me/submissions/608a7c8b-ae37-48bc-8013-c76066d1b17e

import Mathlib

/-!
# The extrapolation inequality (4.19) of the proof of Schneider–Lang, uniformly

Pure real arithmetic; the book does not spell out the uniformity in `u ≥ ET` (blueprint flag 7). With
`K = 2C·6^{n+1} ≥ 8`, `ℓ = log E`, `K U = S₁ E T ℓ`, `N = U/(2C)` and `Z = log (u/T) ≥ ℓ`, every term of the
left side is at most a fraction of `S₁ u Z`:
* (i) `(C + 1) N ≤ U ≤ S₁ u Z / 8`;
* (ii) `C M (1 + log T) + log M! ≤ S₁ u Z / 4`, as `M ≤ 2nu`, `S₁ ≥ 16 n(n+1)(C+1)` and
  `ℓ ≥ 16 n(C+1)(1 + n log S₁ + log 3n)` (`par_p7_M`);
* (iii) the terms with a factor `T` are at most `T Z E / 8 ≤ S₁ u Z / 8`, as `E` is large (`par_p7_T`);
* (iv) `cx T (cF S₁ u / T) = cx cF S₁ u ≤ S₁ u Z / 8`, as `ℓ ≥ 8 |cx| cF`.
`S₁` is chosen first, then `E`.
-/

namespace SchneiderLangExtrapolationIneq

lemma log_factorial_le (k : ℕ) : Real.log (k.factorial : ℝ) ≤ k * Real.log k := by
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos k)
  exact_mod_cast Nat.factorial_le_pow k

/-- `k log k ≤ k log P` for `0 ≤ k ≤ P`. -/
lemma mul_log_le_mul_log {k P : ℝ} (hk : 0 ≤ k) (hkP : k ≤ P) :
    k * Real.log k ≤ k * Real.log P := by
  rcases hk.lt_or_eq with hk | hk
  · exact mul_le_mul_of_nonneg_left (Real.log_le_log hk hkP) hk.le
  · rw [← hk]; simp

lemma log_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x); linarith

/-- (4.19), the terms of order `u log u`: `C M (1 + log T) + log M! ≤ S₁ u Z / 4`. -/
lemma par_p7_M {n : ℕ} {S₁ T ℓ Z C u M lf : ℝ} (hn : 1 ≤ n) (hC : 1 ≤ C) (hS₁1 : 1 ≤ S₁)
    (hT : 1 ≤ T) (hu1 : 1 ≤ u) (hlogu : Real.log u = Real.log T + Z) (hℓZ : ℓ ≤ Z)
    (hℓ : 1 ≤ ℓ) (hTlog : Real.log T ≤ n * Real.log S₁ + n * ℓ)
    (hS₁ : 16 * (n * (n + 1) * (C + 1)) ≤ S₁)
    (hℓ0 : 16 * n * (C + 1) * (1 + n * Real.log S₁ + Real.log (3 * n)) ≤ ℓ)
    (hM0 : 0 ≤ M) (hM : M ≤ 2 * n * u) (hlf : lf ≤ M * Real.log M) :
    C * (M * (1 + Real.log T)) + lf ≤ S₁ * u * Z / 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hupos : 0 < u := by linarith
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hlogS₁ : 0 ≤ Real.log S₁ := Real.log_nonneg hS₁1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hZ0 : 0 ≤ Z := by linarith
  have hnZ : (n : ℝ) * ℓ ≤ n * Z := mul_le_mul_of_nonneg_left hℓZ (by positivity)
  have h2nu : 1 ≤ 2 * (n : ℝ) * u := by
    have := one_le_mul_of_one_le_of_one_le hn' hu1; linarith
  have hlog2nu : Real.log (2 * n * u) = Real.log (2 * n) + Real.log T + Z := by
    rw [Real.log_mul (by positivity) hupos.ne', hlogu]; ring
  have hlog2n : Real.log (2 * n) ≤ Real.log (3 * n) := Real.log_le_log (by positivity) (by linarith)
  have hX : 0 ≤ C * (1 + Real.log T) + Real.log (2 * n * u) := by
    have := Real.log_nonneg h2nu; positivity
  have e1 : C * (M * (1 + Real.log T)) + lf ≤
      2 * n * u * (C * (1 + Real.log T) + Real.log (2 * n * u)) := by
    have hl := mul_log_le_mul_log hM0 hM
    have := mul_le_mul_of_nonneg_right hM hX
    linarith
  have e2 : C * (1 + Real.log T) + Real.log (2 * n * u) ≤
      (C + 1) * (1 + n * Real.log S₁ + Real.log (3 * n)) + (C + 1) * (n + 1) * Z := by
    have f1 : (C + 1) * Real.log T ≤ (C + 1) * (n * Real.log S₁ + n * Z) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have f2 : 0 ≤ C * Real.log (3 * n) := mul_nonneg (by linarith) hlog3n
    have f3 : 0 ≤ C * Z := mul_nonneg (by linarith) hZ0
    rw [hlog2nu]; linarith
  have e3 := mul_le_mul_of_nonneg_right hS₁ (by positivity : (0 : ℝ) ≤ u * Z)
  have e4 := mul_le_mul_of_nonneg_right (hℓ0.trans (hℓZ.trans (le_mul_of_one_le_left hZ0 hS₁1)))
    hupos.le
  have e5 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2 * n * u)
  linarith

/-- (4.19), the terms with a factor `T`: they are at most `T Z E / 8 ≤ S₁ u Z / 8`. -/
lemma par_p7_T {n d : ℕ} {S₁ T E Z C cF u M : ℝ} (hn : 1 ≤ n) (hC : 1 ≤ C) (hcF : 1 ≤ cF)
    (hS₁1 : 1 ≤ S₁) (hT : 1 ≤ T) (hE1 : 1 ≤ E) (hu : E * T ≤ u)
    (hlogu : Real.log u = Real.log T + Z) (hZ1 : 1 ≤ Z)
    (hTlog : Real.log T ≤ n * Real.log S₁ + n * Z)
    (hE : 8 * (C * S₁ + C * Real.log (3 * n) + C * n * Real.log S₁ + C * (n + 1) + n + d +
      Real.log (cF * S₁) + 1) ≤ E) (hM0 : 0 ≤ M) (hM : M ≤ 2 * n * u) :
    C * (T * (S₁ + Real.log (1 + M))) + Real.log n + d * Real.log (T + 1) +
      T * Real.log (cF * S₁ * u / T) ≤ S₁ * u * Z / 8 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTpos : 0 < T := by linarith
  have hu1 : 1 ≤ u := le_trans (one_le_mul_of_one_le_of_one_le hE1 hT) hu
  have hupos : 0 < u := by linarith
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hlogS₁ : 0 ≤ Real.log S₁ := Real.log_nonneg hS₁1
  have hlogcF : 0 ≤ Real.log (cF * S₁) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hcF hS₁1)
  have l1 : Real.log (1 + M) ≤ Real.log (3 * n) + n * Real.log S₁ + (n + 1) * Z := by
    have hnu := one_le_mul_of_one_le_of_one_le hn' hu1
    have := Real.log_le_log (by linarith) (by linarith : (1 : ℝ) + M ≤ 3 * n * u)
    rw [Real.log_mul (by positivity) hupos.ne', hlogu] at this
    linarith
  have l2 : Real.log n ≤ n * T := by
    have := log_le_self_of_one_le hn'
    have : (n : ℝ) ≤ n * T := le_mul_of_one_le_right (by linarith) hT
    linarith
  have l3 : Real.log (T + 1) ≤ T := by
    have := Real.log_le_log (by positivity) (Real.add_one_le_exp T); rwa [Real.log_exp] at this
  have l4 : Real.log (cF * S₁ * u / T) = Real.log (cF * S₁) + Z := by
    rw [mul_div_assoc, Real.log_mul (by positivity) (by positivity),
      Real.log_div hupos.ne' hTpos.ne', hlogu]; ring
  have m1 := mul_le_mul_of_nonneg_left l1 (by positivity : (0 : ℝ) ≤ C * T)
  have m2 := mul_le_mul_of_nonneg_left l3 (by positivity : (0 : ℝ) ≤ d)
  have m3 := mul_le_mul_of_nonneg_left hZ1 (by positivity : (0 : ℝ) ≤ T * (C * S₁ +
    C * Real.log (3 * n) + C * n * Real.log S₁ + n + d + Real.log (cF * S₁)))
  have e2 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ T * Z)
  have e3 := mul_le_mul_of_nonneg_right hu (by linarith : (0 : ℝ) ≤ Z)
  have e4 := mul_le_mul_of_nonneg_right hS₁1 (by positivity : (0 : ℝ) ≤ u * Z)
  rw [l4]
  linarith

end SchneiderLangExtrapolationIneq

open SchneiderLangExtrapolationIneq in
/-- **The extrapolation inequality (4.19) of the proof of Schneider–Lang, uniformly** (DALAG §4.6). -/
theorem solution (n d : ℕ) (C cx cF : ℝ) (hn : 1 ≤ n) (hC : 1 ≤ C)
    (hcF : 1 ≤ cF) :
    ∃ s₀ : ℕ, ∀ S₁ : ℕ, s₀ ≤ S₁ → ∃ e₀ : ℝ, ∀ (T E : ℕ) (U N : ℝ), 1 ≤ T → e₀ ≤ E →
      Real.log T ≤ n * Real.log S₁ + n * Real.log E →
      U = S₁ * (E * T) * Real.log E / (2 * C * 6 ^ (n + 1)) → N = U / (2 * C) →
      ∀ u M : ℕ, E * T ≤ u → M ≤ 2 * n * u →
        C * (N + M * (1 + Real.log T) + T * (S₁ + Real.log (1 + M))) +
          Real.log (M.factorial : ℝ) + Real.log n +
          (d * Real.log (T + 1) + N + T * Real.log (cF * S₁ * u / T) +
            cx * T * (cF * S₁ * u / T)) < u * S₁ * Real.log (u / T) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set K : ℝ := 2 * C * 6 ^ (n + 1) with hK
  have hK8 : 8 ≤ K := by
    have : (6 : ℝ) ≤ 6 ^ (n + 1) := le_self_pow₀ (by norm_num) (by omega)
    rw [hK]; nlinarith
  /- First `S₁ ≥ 16 n(n+1)(C+1)`. -/
  refine ⟨⌈16 * ((n : ℝ) * (n + 1) * (C + 1))⌉₊ + 1, fun S₁ hS₁ => ?_⟩
  have hS₁' : ((⌈16 * ((n : ℝ) * (n + 1) * (C + 1))⌉₊ + 1 : ℕ) : ℝ) ≤ S₁ := by exact_mod_cast hS₁
  push_cast at hS₁'
  have hS₁16 : 16 * ((n : ℝ) * (n + 1) * (C + 1)) ≤ S₁ := by
    linarith [Nat.le_ceil (16 * ((n : ℝ) * (n + 1) * (C + 1)))]
  have hS₁1 : (1 : ℝ) ≤ S₁ := by
    linarith [Nat.cast_nonneg (α := ℝ) ⌈16 * ((n : ℝ) * (n + 1) * (C + 1))⌉₊]
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hlogS₁ : 0 ≤ Real.log S₁ := Real.log_nonneg hS₁1
  set A : ℝ := 1 + n * Real.log S₁ + Real.log (3 * n) with hA
  have hA0 : 0 ≤ A := by positivity
  /- Then `E ≥ 8 (C S₁ + ⋯ + 1)` and `log E ≥ 16 n(C+1) A + 8 |cx| cF + 1`. -/
  refine ⟨max (8 * (C * S₁ + C * Real.log (3 * n) + C * n * Real.log S₁ + C * (n + 1) + n + d +
    Real.log (cF * S₁) + 1)) (Real.exp (16 * n * (C + 1) * A + 8 * |cx| * cF + 1)), ?_⟩
  intro T E U N hT hE hTlog hU hN u M hu hM
  have hEf : 8 * (C * S₁ + C * Real.log (3 * n) + C * n * Real.log S₁ + C * (n + 1) + n + d +
      Real.log (cF * S₁) + 1) ≤ E := le_trans (le_max_left _ _) hE
  have hEexp : Real.exp (16 * n * (C + 1) * A + 8 * |cx| * cF + 1) ≤ E :=
    le_trans (le_max_right _ _) hE
  have hℓ : 16 * n * (C + 1) * A + 8 * |cx| * cF + 1 ≤ Real.log E := by
    have := Real.log_le_log (Real.exp_pos _) hEexp; rwa [Real.log_exp] at this
  have hb0 : 0 ≤ 16 * n * (C + 1) * A := by positivity
  have hcx0 : 0 ≤ 8 * |cx| * cF := by positivity
  have hcx : 8 * cx * cF ≤ 8 * |cx| * cF :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self cx]) (by linarith)
  have hE1 : (1 : ℝ) ≤ E := le_trans (Real.one_le_exp (by linarith)) hEexp
  have hEpos : (0 : ℝ) < E := by linarith
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hu' : (E : ℝ) * T ≤ u := by exact_mod_cast hu
  have hM' : (M : ℝ) ≤ 2 * n * u := by exact_mod_cast hM
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_mul_of_one_le_of_one_le hE1 hT1) hu'
  have hupos : (0 : ℝ) < u := by linarith
  have hUval : K * U = S₁ * (E * T) * Real.log E := by rw [hU]; field_simp
  have hU0 : 0 ≤ U := by
    rw [hU]; have : 0 ≤ Real.log E := by linarith
    positivity
  set Z := Real.log (u / T) with hZ
  have hlogu : Real.log u = Real.log T + Z := by rw [hZ, Real.log_div hupos.ne' hTpos.ne']; ring
  have hℓZ : Real.log E ≤ Z :=
    Real.log_le_log hEpos (by rw [le_div_iff₀ hTpos]; linarith)
  have hnZ : (n : ℝ) * Real.log E ≤ n * Z := mul_le_mul_of_nonneg_left hℓZ (by positivity)
  /- (i) `(C + 1) N ≤ U ≤ S₁ u Z / 8`. -/
  have hi : (C + 1) * N ≤ S₁ * u * Z / 8 := by
    have e1 : (C + 1) * N ≤ U := by
      have : (C + 1) * U ≤ 2 * C * U := mul_le_mul_of_nonneg_right (by linarith) hU0
      rw [hN, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      linarith
    have e2 := mul_le_mul_of_nonneg_left (mul_le_mul hu' hℓZ (by linarith) hupos.le)
      (by linarith : (0 : ℝ) ≤ S₁)
    have e3 : 8 * U ≤ K * U := mul_le_mul_of_nonneg_right hK8 hU0
    linarith
  /- (ii) and (iii). -/
  have hii := par_p7_M hn hC hS₁1 hT1 hu1 hlogu hℓZ (by linarith) hTlog hS₁16 (by linarith)
    (Nat.cast_nonneg M) hM' (log_factorial_le M)
  have hiii := par_p7_T (d := d) hn hC hcF hS₁1 hT1 hE1 hu' hlogu (by linarith) (by linarith)
    hEf (Nat.cast_nonneg M) hM'
  /- (iv) `cx T (cF S₁ u / T) = cx cF S₁ u ≤ S₁ u Z / 8`. -/
  have hiv : cx * T * (cF * S₁ * u / T) ≤ S₁ * u * Z / 8 := by
    have e1 : cx * T * (cF * S₁ * u / T) = 8 * cx * cF * (S₁ * u) / 8 := by
      field_simp
    have := mul_le_mul_of_nonneg_right (by linarith : 8 * cx * cF ≤ Z)
      (by positivity : (0 : ℝ) ≤ S₁ * u)
    rw [e1]; linarith
  have hpos : 0 < S₁ * u * Z := by
    have : 0 < Z := by linarith
    positivity
  linarith
