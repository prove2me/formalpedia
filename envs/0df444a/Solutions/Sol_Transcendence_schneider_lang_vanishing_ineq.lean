-- Prove2me | solution 1 for Transcendence.schneider_lang_vanishing_ineq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:35:02.867127+00:00
-- url     : https://prove2.me/submissions/15b11294-3289-4aff-a019-79ab4ad17029

import Mathlib

/-!
# The vanishing inequality (4.17) of the proof of Schneider–Lang

Pure real arithmetic. With `K = 2C·6^{n+1}`, `ℓ = log E`, `K U = S₁ E T ℓ` and `C N = U/2`, and `k < P = nET`:
* `C k (1 + log T) + log k! ≤ P (C (1 + log T) + log P) ≤ U/4`, since `S₁ ≥ 8K n(n+1)(C+1)` and
  `ℓ ≥ 8K n(C+1)(1 + n log S₁ + log 3n)` (`par_p6_k`);
* `C T (S₁ + log (1 + k)) ≤ U/8`, since `E ≥ 8KC (S₁ + log 3n + n log S₁ + n + 1)` (`par_p6_T`);
so the left side is at most `U/2 + U/4 + U/8 < U`. `S₁` is chosen first, then `E`.
-/

namespace SchneiderLangVanishingIneq

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

/-- (4.17), the terms in `k`: `C k (1 + log T) + log k! ≤ U/4`. -/
lemma par_p6_k {n : ℕ} {S₁ T E ℓ K U C : ℝ} (hn : 1 ≤ n) (hC : 1 ≤ C) (hS₁1 : 1 ≤ S₁)
    (hT : 1 ≤ T) (hE1 : 1 ≤ E) (hℓ : 1 ≤ ℓ) (hK : 0 < K) (hUval : K * U = S₁ * (E * T) * ℓ)
    (hEℓ : Real.log E = ℓ) (hTlog : Real.log T ≤ n * Real.log S₁ + n * ℓ)
    (hS₁ : 8 * K * (n * (n + 1) * (C + 1)) ≤ S₁)
    (hℓ0 : 8 * K * n * (C + 1) * (1 + n * Real.log S₁ + Real.log (3 * n)) ≤ ℓ)
    {k lf : ℝ} (hk0 : 0 ≤ k) (hkP : k + 1 ≤ n * (E * T)) (hlf : lf ≤ k * Real.log k) :
    C * (k * (1 + Real.log T)) + lf ≤ U / 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hEpos : 0 < E := by linarith
  have hTpos : 0 < T := by linarith
  set P : ℝ := n * (E * T) with hP
  have hP1 : 1 ≤ P := one_le_mul_of_one_le_of_one_le hn' (one_le_mul_of_one_le_of_one_le hE1 hT)
  have hlogP : Real.log P = Real.log n + Real.log T + ℓ := by
    rw [hP, Real.log_mul (by positivity) (by positivity), Real.log_mul hEpos.ne' hTpos.ne', hEℓ]
    ring
  have hlogn : Real.log n ≤ Real.log (3 * n) := Real.log_le_log (by positivity) (by linarith)
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hX : 0 ≤ C * (1 + Real.log T) + Real.log P := by
    have := Real.log_nonneg hP1; have := Real.log_nonneg hT; positivity
  have h1 : C * (k * (1 + Real.log T)) + lf ≤ P * (C * (1 + Real.log T) + Real.log P) := by
    have hl := mul_log_le_mul_log hk0 (by linarith : k ≤ P)
    have := mul_le_mul_of_nonneg_right (by linarith : k ≤ P) hX
    linarith
  have h2 : C * (1 + Real.log T) + Real.log P ≤
      (C + 1) * (1 + n * Real.log S₁ + Real.log (3 * n)) + (C + 1) * (n + 1) * ℓ := by
    have e1 : (C + 1) * Real.log T ≤ (C + 1) * (n * Real.log S₁ + n * ℓ) :=
      mul_le_mul_of_nonneg_left hTlog (by linarith)
    have e2 : 0 ≤ C * Real.log (3 * n) := mul_nonneg (by linarith) hlog3n
    have e3 : 0 ≤ C * ℓ := mul_nonneg (by linarith) (by linarith)
    rw [hlogP]; linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ P)
  have h4 : K * (P * ((C + 1) * (n + 1) * ℓ)) ≤ K * U / 8 := by
    have := mul_le_mul_of_nonneg_right hS₁ (by positivity : (0 : ℝ) ≤ E * T * ℓ)
    rw [hUval, hP]; linarith
  have h5 : K * (P * ((C + 1) * (1 + n * Real.log S₁ + Real.log (3 * n)))) ≤ K * U / 8 := by
    have e2 : ℓ ≤ S₁ * ℓ := le_mul_of_one_le_left (by linarith) hS₁1
    have := mul_le_mul_of_nonneg_right (hℓ0.trans e2) (by positivity : (0 : ℝ) ≤ E * T)
    rw [hUval, hP]; linarith
  exact le_of_mul_le_mul_left (by linarith [mul_le_mul_of_nonneg_left (h1.trans h3) hK.le] :
    K * (C * (k * (1 + Real.log T)) + lf) ≤ K * (U / 4)) hK

/-- (4.17), the terms with a factor `T`: `C T (S₁ + log (1 + k)) ≤ U/8`. -/
lemma par_p6_T {n : ℕ} {S₁ T E ℓ K U C : ℝ} (hn : 1 ≤ n) (hC : 1 ≤ C) (hS₁1 : 1 ≤ S₁)
    (hT : 1 ≤ T) (hE1 : 1 ≤ E) (hℓ : 1 ≤ ℓ) (hK : 0 < K) (hUval : K * U = S₁ * (E * T) * ℓ)
    (hEℓ : Real.log E = ℓ) (hTlog : Real.log T ≤ n * Real.log S₁ + n * ℓ)
    (hE : 8 * K * (C * (S₁ + Real.log (3 * n) + n * Real.log S₁ + n + 1)) ≤ E)
    {k : ℝ} (hk0 : 0 ≤ k) (hkP : k + 1 ≤ n * (E * T)) :
    C * (T * (S₁ + Real.log (1 + k))) ≤ U / 8 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hEpos : 0 < E := by linarith
  have hTpos : 0 < T := by linarith
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hlogS₁ : 0 ≤ Real.log S₁ := Real.log_nonneg hS₁1
  have hl : Real.log (1 + k) ≤ Real.log (3 * n) + n * Real.log S₁ + (n + 1) * ℓ := by
    have h := Real.log_le_log (by positivity) (by linarith : (1 : ℝ) + k ≤ n * (E * T))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hEpos.ne' hTpos.ne', hEℓ] at h
    have : Real.log n ≤ Real.log (3 * n) := Real.log_le_log (by positivity) (by linarith)
    linarith
  have e1 : S₁ + Real.log (1 + k) ≤ (S₁ + Real.log (3 * n) + n * Real.log S₁ + n + 1) * ℓ := by
    have g1 : S₁ ≤ S₁ * ℓ := le_mul_of_one_le_right (by linarith) hℓ
    have g2 : Real.log (3 * n) ≤ Real.log (3 * n) * ℓ := le_mul_of_one_le_right hlog3n hℓ
    have g3 : n * Real.log S₁ ≤ n * Real.log S₁ * ℓ := le_mul_of_one_le_right (by positivity) hℓ
    linarith
  have e5 := mul_le_mul_of_nonneg_right hS₁1 (by positivity : (0 : ℝ) ≤ E * T * ℓ)
  have h6 : K * (C * (T * (S₁ + Real.log (1 + k)))) ≤ K * (U / 8) := by
    have f1 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ K * C * T)
    have f2 := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ T * ℓ)
    linarith
  exact le_of_mul_le_mul_left h6 hK

end SchneiderLangVanishingIneq

open SchneiderLangVanishingIneq in
/-- **The vanishing inequality (4.17) of the proof of Schneider–Lang** (DALAG §4.6). -/
theorem solution (n : ℕ) (C : ℝ) (hn : 1 ≤ n) (hC : 1 ≤ C) :
    ∃ s₀ : ℕ, ∀ S₁ : ℕ, s₀ ≤ S₁ → ∃ e₀ : ℝ, ∀ (T E : ℕ) (U N : ℝ), 1 ≤ T → e₀ ≤ E →
      Real.log T ≤ n * Real.log S₁ + n * Real.log E →
      U = S₁ * (E * T) * Real.log E / (2 * C * 6 ^ (n + 1)) → N = U / (2 * C) →
      ∀ k : ℕ, k < n * (E * T) →
        C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k))) +
          Real.log (k.factorial : ℝ) < U := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set K : ℝ := 2 * C * 6 ^ (n + 1) with hK
  have hKpos : 0 < K := by positivity
  /- First `S₁ ≥ 8K n(n+1)(C+1)`. -/
  refine ⟨⌈8 * K * (n * (n + 1) * (C + 1))⌉₊ + 1, fun S₁ hS₁ => ?_⟩
  have hS₁' : ((⌈8 * K * (n * (n + 1) * (C + 1))⌉₊ + 1 : ℕ) : ℝ) ≤ S₁ := by exact_mod_cast hS₁
  push_cast at hS₁'
  have hS₁K : 8 * K * (n * (n + 1) * (C + 1)) ≤ S₁ := by
    linarith [Nat.le_ceil (8 * K * (n * (n + 1) * (C + 1)))]
  have hS₁1 : (1 : ℝ) ≤ S₁ := by
    linarith [Nat.cast_nonneg (α := ℝ) ⌈8 * K * (n * (n + 1) * (C + 1))⌉₊]
  have hlog3n : 0 ≤ Real.log (3 * n) := Real.log_nonneg (by linarith)
  have hlogS₁ : 0 ≤ Real.log S₁ := Real.log_nonneg hS₁1
  set A : ℝ := 1 + n * Real.log S₁ + Real.log (3 * n) with hA
  have hA0 : 0 ≤ A := by positivity
  /- Then `E ≥ 8KC (S₁ + log 3n + n log S₁ + n + 1)` and `log E ≥ 8K n(C+1) A + 1`. -/
  refine ⟨max (8 * K * (C * (S₁ + Real.log (3 * n) + n * Real.log S₁ + n + 1)))
    (Real.exp (8 * K * n * (C + 1) * A + 1)), ?_⟩
  intro T E U N hT hE hTlog hU hN k hk
  have hEe : 8 * K * (C * (S₁ + Real.log (3 * n) + n * Real.log S₁ + n + 1)) ≤ E :=
    le_trans (le_max_left _ _) hE
  have hEexp : Real.exp (8 * K * n * (C + 1) * A + 1) ≤ E := le_trans (le_max_right _ _) hE
  have hℓ : 8 * K * n * (C + 1) * A + 1 ≤ Real.log E := by
    have := Real.log_le_log (Real.exp_pos _) hEexp; rwa [Real.log_exp] at this
  have hℓ0 : 0 ≤ 8 * K * n * (C + 1) * A := by positivity
  have hE1 : (1 : ℝ) ≤ E := le_trans (Real.one_le_exp (by linarith)) hEexp
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hUval : K * U = S₁ * (E * T) * Real.log E := by rw [hU]; field_simp
  have hCN : C * N = U / 2 := by rw [hN]; field_simp
  have hUpos : 0 < U := by
    rw [hU]; have : 0 < Real.log E := by linarith
    positivity
  have hk' : (k : ℝ) + 1 ≤ n * (E * T) := by exact_mod_cast hk
  have h1 := par_p6_k hn hC hS₁1 hT1 hE1 (by linarith) hKpos hUval rfl hTlog hS₁K (by linarith)
    (Nat.cast_nonneg k) hk' (log_factorial_le k)
  have h2 := par_p6_T hn hC hS₁1 hT1 hE1 (by linarith) hKpos hUval rfl hTlog hEe (Nat.cast_nonneg k)
    hk'
  have e : C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k))) =
      C * N + C * (k * (1 + Real.log T)) + C * (T * (S₁ + Real.log (1 + k))) := by ring
  rw [e, hCN]
  linarith
