-- Prove2me | solution 1 for Transcendence.exists_schneider_lang_parameters
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:17:21.212092+00:00
-- url     : https://prove2.me/submissions/d3b38dfd-079b-46d9-b790-9ae97b1ce3e6

import Mathlib
import Theorems.Thm_Transcendence_schneider_lang_vanishing_ineq
import Theorems.Thm_Transcendence_schneider_lang_extrapolation_ineq

/-!
# The parameters of the proof of Schneider–Lang

Waldschmidt's §4.6, conditions (4.15)–(4.19). First `S₁` is large enough for (4.17) and (4.19)
(`schneider_lang_vanishing_ineq`, `schneider_lang_extrapolation_ineq`), then `m` is large, and
`T = (S₁m)ⁿ`, `E = S₁^{d-1-n} m^{d-n}`, so that `E ≥ m` and `T^d = (S₁ E T)ⁿ`;
`U = S₁ E T log E / K`, `K = 2C·6^{n+1}`, and `N = U/(2C)`. The hypotheses of node 3 are (P1)–(P5):
(P2) is `log E ≥ 1`, and the others are `par_p1`, `par_p3`, `par_p4`, `par_p5`.
-/

namespace ExistsSchneiderLangParameters

/-- (P1) -/
lemma par_p1 {n : ℕ} {S₁ T E ℓ K U N : ℝ} (hS₁ : 1 ≤ S₁) (hT : 1 ≤ T) (hℓ : 1 ≤ ℓ)
    (hK : 0 < K) (hUval : K * U = S₁ * (E * T) * ℓ) (hN : 0 ≤ N) (hE : 6 * (n : ℝ) ^ 2 * K ≤ E) :
    12 * (n : ℝ) ^ 2 ≤ N + U + U := by
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have h1 : E ≤ S₁ * (E * T) * ℓ := by
    calc E = 1 * (E * 1) * 1 := by ring
      _ ≤ S₁ * (E * T) * ℓ := by gcongr
  have h2 : 6 * (n : ℝ) ^ 2 * K ≤ U * K := by linarith
  have h3 : 6 * (n : ℝ) ^ 2 ≤ U := le_of_mul_le_mul_right h2 hK
  linarith

/-- (P3) -/
lemma par_p3 {S₁ T E ℓ K U N : ℝ} (hS₁ : 1 ≤ S₁) (hT : 1 ≤ T) (hℓ : 1 ≤ ℓ) (hK : 0 < K)
    (hUval : K * U = S₁ * (E * T) * ℓ) (hN : 0 ≤ N) (hE : 3 * K ≤ E) (hEℓ : Real.log E = ℓ) :
    E ≤ Real.exp ((N + U + U) / 6) := by
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity) hE
  rw [← Real.exp_log hEpos, hEℓ]
  apply Real.exp_le_exp.mpr
  have h1 : 3 * K ≤ S₁ * (E * T) := by
    calc 3 * K ≤ 1 * (E * 1) := by linarith
      _ ≤ S₁ * (E * T) := by gcongr
  have h2 : 3 * K * ℓ ≤ K * U := by rw [hUval]; exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : 3 * ℓ ≤ U := by nlinarith
  linarith

/-- (P4): `(T+1)^d R^T e^{cx T R} ≤ e^U` for `R = E (cy + 2) S₁`. -/
lemma par_p4 {d T : ℕ} {S₁ E ℓ K U cx cy : ℝ} (hS₁ : 1 ≤ S₁) (hT : 1 ≤ T) (hℓ : 1 ≤ ℓ)
    (hK : 0 < K) (hcy : 0 ≤ cy) (hE1 : 1 ≤ E)
    (hUval : K * U = S₁ * (E * T) * ℓ) (hEℓ : Real.log E = ℓ)
    (hE : 2 * K * (d + 1 + Real.log ((cy + 2) * S₁)) ≤ E) (hℓ0 : 2 * K * cx * (cy + 2) ≤ ℓ) :
    ((T : ℝ) + 1) ^ d * (E * ((cy + 2) * S₁)) ^ T * Real.exp (cx * T * (E * ((cy + 2) * S₁))) ≤
      Real.exp U := by
  set R : ℝ := E * ((cy + 2) * S₁) with hR
  set lc := Real.log ((cy + 2) * S₁) with hlc
  have hEpos : 0 < E := by linarith
  have hRpos : 0 < R := by positivity
  have hlc0 : 0 ≤ lc := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hS₁)
  have hlogR : Real.log R = ℓ + lc := by rw [hR, Real.log_mul hEpos.ne' (by positivity), hEℓ]
  have h1 : ((T : ℝ) + 1) ^ d ≤ Real.exp (d * T) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (T : ℝ)]) _
  have h2 : R ^ T = Real.exp (T * Real.log R) := by
    rw [← Real.exp_log hRpos, ← Real.exp_nat_mul, Real.log_exp]
  have hexp : d * T + T * Real.log R + cx * T * R ≤ U := by
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have e1 := mul_le_mul_of_nonneg_right hℓ0 (by positivity : (0 : ℝ) ≤ S₁ * E * T)
    have e2 := mul_le_mul_of_nonneg_left hℓ (add_nonneg (Nat.cast_nonneg d) hlc0)
    have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ K * T)
    have e4 := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ T * ℓ)
    have e5 := mul_le_mul_of_nonneg_right hS₁ (by positivity : (0 : ℝ) ≤ E * T * ℓ)
    have : K * (d * T + T * Real.log R + cx * T * R) ≤ K * U := by
      rw [hUval, hlogR, hR]; linarith
    exact le_of_mul_le_mul_left this hK
  calc ((T : ℝ) + 1) ^ d * R ^ T * Real.exp (cx * T * R)
      ≤ Real.exp (d * T) * Real.exp (T * Real.log R) * Real.exp (cx * T * R) := by
        rw [h2]; gcongr
    _ = Real.exp (d * T + T * Real.log R + cx * T * R) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hexp

/-- (P5) -/
lemma par_p5 {n d T : ℕ} {S₁ E ℓ K U N C : ℝ} (hn : 1 ≤ n) (hC : 1 ≤ C) (hℓ : 0 ≤ ℓ)
    (hK : K = 2 * C * 6 ^ (n + 1))
    (hUval : K * U = S₁ * (E * T) * ℓ) (hU : 0 ≤ U) (hN : N = U / (2 * C))
    (hTd : (T : ℝ) ^ d = (S₁ * (E * T)) ^ n) :
    (2 * (N + U + U)) ^ (n + 1) ≤ ((T : ℝ) + 1) ^ d * N * ℓ ^ n := by
  have hKpos : 0 < K := by rw [hK]; positivity
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : (1 : ℝ) ≤ 6 ^ (n + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hNU : N ≤ U := by rw [hN, div_le_iff₀ (by positivity)]; nlinarith
  have h1 : 2 * (N + U + U) ≤ 6 * U := by linarith
  have h2 : (2 * (N + U + U)) ^ (n + 1) ≤ (6 * U) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have hKn : K ≤ K ^ n := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ n := pow_le_pow_right₀ hK1 hn
  have h4 : ((T : ℝ) + 1) ^ d * N * ℓ ^ n ≥ K ^ n * U ^ n * N := by
    have e : (T : ℝ) ^ d * ℓ ^ n = (K * U) ^ n := by rw [hTd, hUval]; ring
    calc ((T : ℝ) + 1) ^ d * N * ℓ ^ n ≥ (T : ℝ) ^ d * N * ℓ ^ n := by
          have : (T : ℝ) ^ d ≤ ((T : ℝ) + 1) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) _
          have h0 : 0 ≤ N * ℓ ^ n := mul_nonneg hN0 (pow_nonneg hℓ _)
          nlinarith
      _ = (K * U) ^ n * N := by rw [← e]; ring
      _ = K ^ n * U ^ n * N := by rw [mul_pow]
  have h6' : 6 ^ (n + 1) * U = K * N := by
    rw [hN, hK]; field_simp
  calc (2 * (N + U + U)) ^ (n + 1) ≤ (6 * U) ^ (n + 1) := h2
    _ = U ^ n * (6 ^ (n + 1) * U) := by ring
    _ = U ^ n * (K * N) := by rw [h6']
    _ ≤ U ^ n * (K ^ n * N) := by gcongr
    _ = K ^ n * U ^ n * N := by ring
    _ ≤ ((T : ℝ) + 1) ^ d * N * ℓ ^ n := h4

end ExistsSchneiderLangParameters

open ExistsSchneiderLangParameters in
/-- **The parameters of the proof of Schneider–Lang** (DALAG §4.6, (4.15)–(4.19)). -/
theorem solution (n d : ℕ) (C cx cy cF : ℝ) (hn : 1 ≤ n)
    (hd : n + 1 ≤ d) (hC : 1 ≤ C) (hcx : 0 ≤ cx) (hcy : 0 ≤ cy) (hcF : 1 ≤ cF) :
    ∃ (S₁ T E : ℕ) (U N : ℝ), 1 ≤ S₁ ∧ 1 ≤ T ∧ 1 ≤ E ∧ 0 < U ∧ 0 < N ∧
      (12 * (n : ℝ) ^ 2 ≤ N + U + U ∧ Real.exp 1 ≤ (E : ℝ) ∧
        (E : ℝ) ≤ Real.exp ((N + U + U) / 6) ∧
        ((T : ℝ) + 1) ^ d * ((E : ℝ) * ((cy + 2) * S₁)) ^ T *
          Real.exp (cx * T * ((E : ℝ) * ((cy + 2) * S₁))) ≤ Real.exp U ∧
        (2 * (N + U + U)) ^ (n + 1) ≤ ((T : ℝ) + 1) ^ d * N * Real.log (E : ℝ) ^ n) ∧
      (∀ k : ℕ, k < n * (E * T) →
        C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k))) +
          Real.log (k.factorial : ℝ) < U) ∧
      ∀ u M : ℕ, E * T ≤ u → M ≤ 2 * n * u →
        C * (N + M * (1 + Real.log T) + T * (S₁ + Real.log (1 + M))) +
          Real.log (M.factorial : ℝ) + Real.log n +
          (d * Real.log (T + 1) + N + T * Real.log (cF * S₁ * u / T) +
            cx * T * (cF * S₁ * u / T)) < u * S₁ * Real.log (u / T) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  /- `S₁` large for (4.17) and (4.19). -/
  obtain ⟨s₆, hs₆⟩ := Transcendence.schneider_lang_vanishing_ineq n C hn hC
  obtain ⟨s₇, hs₇⟩ := Transcendence.schneider_lang_extrapolation_ineq n d C cx cF hn hC hcF
  obtain ⟨e₆, he₆⟩ := hs₆ (s₆ + s₇ + 1) (by omega)
  obtain ⟨e₇, he₇⟩ := hs₇ (s₆ + s₇ + 1) (by omega)
  set S₁ : ℕ := s₆ + s₇ + 1 with hS₁
  have hS₁1 : (1 : ℝ) ≤ S₁ := by exact_mod_cast (show 1 ≤ S₁ by omega)
  have hKpos : (0 : ℝ) < 2 * C * 6 ^ (n + 1) := by positivity
  have hlc : 0 ≤ Real.log ((cy + 2) * S₁) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hS₁1)
  /- `m` large, `T = (S₁ m)ⁿ`, `E = S₁^{d-1-n} m^{d-n} ≥ m`. -/
  set X : ℝ := 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)) + 3 * (2 * C * 6 ^ (n + 1)) +
    2 * (2 * C * 6 ^ (n + 1)) * (d + 1 + Real.log ((cy + 2) * S₁)) +
    Real.exp (2 * (2 * C * 6 ^ (n + 1)) * cx * (cy + 2) + 1) with hX
  set m : ℕ := ⌈max (max e₆ e₇) X⌉₊ + 1 with hm
  have hmX : max (max e₆ e₇) X ≤ m := by
    have := Nat.le_ceil (max (max e₆ e₇) X); rw [hm]; push_cast; linarith
  obtain ⟨e, rfl⟩ : ∃ e, d = n + 1 + e := ⟨d - (n + 1), by omega⟩
  have hmE : m ≤ S₁ ^ e * m ^ (e + 1) := by
    calc m = 1 * m ^ 1 := by ring
      _ ≤ S₁ ^ e * m ^ (e + 1) :=
        Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
  set T : ℕ := (S₁ * m) ^ n with hT
  set E : ℕ := S₁ ^ e * m ^ (e + 1) with hE
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hmE' : (m : ℝ) ≤ E := by exact_mod_cast hmE
  have hE6 : e₆ ≤ E := by linarith [le_max_left e₆ e₇, le_max_left (max e₆ e₇) X]
  have hE7 : e₇ ≤ E := by linarith [le_max_right e₆ e₇, le_max_left (max e₆ e₇) X]
  have hEX : X ≤ E := by linarith [le_max_right (max e₆ e₇) X]
  have hexpL := Real.exp_pos (2 * (2 * C * 6 ^ (n + 1)) * cx * (cy + 2) + 1)
  have hEpos : (0 : ℝ) < E := by
    have : (0 : ℝ) ≤ 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)) + 3 * (2 * C * 6 ^ (n + 1)) +
      2 * (2 * C * 6 ^ (n + 1)) * ((n + 1 + e : ℕ) + 1 + Real.log ((cy + 2) * S₁)) := by positivity
    linarith
  have hℓ : 2 * (2 * C * 6 ^ (n + 1)) * cx * (cy + 2) + 1 ≤ Real.log E := by
    have h0 : (0 : ℝ) ≤ 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)) + 3 * (2 * C * 6 ^ (n + 1)) +
      2 * (2 * C * 6 ^ (n + 1)) * ((n + 1 + e : ℕ) + 1 + Real.log ((cy + 2) * S₁)) := by positivity
    have := Real.log_le_log (Real.exp_pos _) (show Real.exp (2 * (2 * C * 6 ^ (n + 1)) * cx *
      (cy + 2) + 1) ≤ E by linarith)
    rwa [Real.log_exp] at this
  have hL0 : 0 ≤ 2 * (2 * C * 6 ^ (n + 1)) * cx * (cy + 2) := by positivity
  have hℓ1 : 1 ≤ Real.log E := by linarith
  have hE1' : (1 : ℝ) ≤ E := by
    rw [← Real.exp_log hEpos]; exact Real.one_le_exp (by linarith)
  have hTlog : Real.log T ≤ n * Real.log S₁ + n * Real.log E := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [hT]; push_cast
    rw [Real.log_pow, Real.log_mul (by positivity) hmpos.ne']
    have := Real.log_le_log hmpos hmE'
    nlinarith
  have hTd : (T : ℝ) ^ (n + 1 + e) = ((S₁ : ℝ) * ((E : ℝ) * T)) ^ n := by
    rw [hT, hE]; push_cast; ring
  /- `U` and `N`. -/
  set U : ℝ := S₁ * (E * T) * Real.log E / (2 * C * 6 ^ (n + 1)) with hU
  set N : ℝ := U / (2 * C) with hN
  have hUval : 2 * C * 6 ^ (n + 1) * U = S₁ * (E * T) * Real.log E := by rw [hU]; field_simp
  have hUpos : 0 < U := by
    rw [hU]; have : (0 : ℝ) < Real.log E := by linarith
    positivity
  have hNpos : 0 < N := by rw [hN]; positivity
  have hX6 : 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)) ≤ (E : ℝ) := by
    have : 0 ≤ 2 * (2 * C * 6 ^ (n + 1)) * ((n + 1 + e : ℕ) + 1 + Real.log ((cy + 2) * S₁)) := by
      positivity
    linarith
  have hX3 : 3 * (2 * C * 6 ^ (n + 1)) ≤ (E : ℝ) := by
    have : 0 ≤ 2 * (2 * C * 6 ^ (n + 1)) * ((n + 1 + e : ℕ) + 1 + Real.log ((cy + 2) * S₁)) := by
      positivity
    linarith [(by positivity : (0 : ℝ) ≤ 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)))]
  have hX4 : 2 * (2 * C * 6 ^ (n + 1)) * ((n + 1 + e : ℕ) + 1 + Real.log ((cy + 2) * S₁)) ≤
      (E : ℝ) := by
    linarith [(by positivity : (0 : ℝ) ≤ 6 * n ^ 2 * (2 * C * 6 ^ (n + 1)))]
  refine ⟨S₁, T, E, U, N, by omega, hT1, by exact_mod_cast hE1', hUpos, hNpos, ⟨?_, ?_, ?_, ?_, ?_⟩,
    he₆ T E U N hT1 hE6 hTlog hU hN, he₇ T E U N hT1 hE7 hTlog hU hN⟩
  · exact par_p1 hS₁1 hT1' hℓ1 hKpos hUval hNpos.le hX6
  · rw [← Real.exp_log hEpos]; exact Real.exp_le_exp.mpr hℓ1
  · exact par_p3 hS₁1 hT1' hℓ1 hKpos hUval hNpos.le hX3 rfl
  · exact par_p4 hS₁1 hT1 hℓ1 hKpos hcy hE1' hUval rfl hX4 (by linarith)
  · exact par_p5 hn hC (by linarith) rfl hUval hUpos.le hN hTd
