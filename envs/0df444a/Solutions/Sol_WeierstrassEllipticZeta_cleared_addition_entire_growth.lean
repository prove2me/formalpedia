-- Prove2me | solution 1 for WeierstrassEllipticZeta.cleared_addition_entire_growth
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T14:07:45.633676+00:00
-- url     : https://prove2.me/submissions/f2a1f8e2-20c2-4c1f-920d-7eb0769e9b1c

import Theorems.Thm_TranscendenceTheory_exists_entire_monomial_regularization
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Tactic.FinCases

noncomputable section

open Finset Set

open WeierstrassEllipticZeta

private lemma norm_regularized_linear (s x a : ℂ) (B V : ℝ)
    (hB : 1 ≤ B) (hV : 1 ≤ V) (hs : ‖s‖ ≤ B) (hx : ‖x‖ ≤ B)
    (ha : ‖a‖ ≤ V) (k : ℕ) (hk : 1 ≤ k) :
    ‖x + a * s ^ k‖ ≤ 2 * V * B ^ k := by
  calc
    _ ≤ ‖x‖ + ‖a‖ * ‖s‖ ^ k := by simpa using norm_add_le x (a * s ^ k)
    _ ≤ B + V * B ^ k := by gcongr
    _ ≤ B ^ k + V * B ^ k := by
      gcongr
      simpa using pow_le_pow_right₀ hB hk
    _ ≤ 2 * V * B ^ k := by
      nlinarith [mul_le_mul_of_nonneg_right hV (pow_nonneg (by linarith : 0 ≤ B) k)]

private lemma cleared_factor_bounds (s x y z a b d : ℂ) (B V : ℝ)
    (hB : 1 ≤ B) (hV : 1 ≤ V)
    (hs : ‖s‖ ≤ B) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) (hz : ‖z‖ ≤ B)
    (ha : ‖a‖ ≤ V) (hb : ‖b‖ ≤ V) (hd : ‖d‖ ≤ V) :
    ‖s‖ ≤ 36 * V ^ 3 * B ^ 6 ∧
    ‖2 * (b * s ^ 2 - y)‖ ≤ 36 * V ^ 3 * B ^ 6 ∧
    ‖-4 * (y + b * s ^ 2) * (b * s ^ 2 - y) ^ 2 +
      (d * s ^ 3 - z) ^ 2‖ ≤ 36 * V ^ 3 * B ^ 6 ∧
    ‖2 * (x + a * s) * (b * s ^ 2 - y) + (d * s ^ 3 - z)‖ ≤
      36 * V ^ 3 * B ^ 6 := by
  have hB0 : 0 ≤ B := by linarith
  have hV0 : 0 ≤ V := by linarith
  have h1 : ‖x + a * s‖ ≤ 2 * V * B := by
    simpa using norm_regularized_linear s x a B V hB hV hs hx ha 1 le_rfl
  have h2 : ‖b * s ^ 2 - y‖ ≤ 2 * V * B ^ 2 := by
    simpa [sub_eq_add_neg, add_comm] using
      norm_regularized_linear s (-y) b B V hB hV hs (by simpa) hb 2 (by omega)
  have h2' := norm_regularized_linear s y b B V hB hV hs hy hb 2 (by omega)
  have h3 : ‖d * s ^ 3 - z‖ ≤ 2 * V * B ^ 3 := by
    simpa [sub_eq_add_neg, add_comm] using
      norm_regularized_linear s (-z) d B V hB hV hs (by simpa) hd 3 (by omega)
  have hVp : V ≤ V ^ 3 := by simpa using pow_le_pow_right₀ hV (by omega : 1 ≤ 3)
  have hVp2 : V ^ 2 ≤ V ^ 3 := pow_le_pow_right₀ hV (by omega)
  have hB26 : B ^ 2 ≤ B ^ 6 := pow_le_pow_right₀ hB (by omega)
  have hB36 : B ^ 3 ≤ B ^ 6 := pow_le_pow_right₀ hB (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      ‖s‖ ≤ B := hs
      _ ≤ B ^ 6 := by simpa using pow_le_pow_right₀ hB (by omega : 1 ≤ 6)
      _ ≤ 36 * V ^ 3 * B ^ 6 := by
        have : 1 ≤ V ^ 3 := one_le_pow₀ hV
        nlinarith [pow_nonneg hB0 6]
  · calc
      _ = 2 * ‖b * s ^ 2 - y‖ := by simp
      _ ≤ 2 * (2 * V * B ^ 2) := by gcongr
      _ = 4 * V * B ^ 2 := by ring
      _ ≤ 36 * V ^ 3 * B ^ 6 := by gcongr; norm_num
  · calc
      _ ≤ ‖-4 * (y + b * s ^ 2) * (b * s ^ 2 - y) ^ 2‖ +
          ‖(d * s ^ 3 - z) ^ 2‖ := norm_add_le _ _
      _ = 4 * ‖y + b * s ^ 2‖ * ‖b * s ^ 2 - y‖ ^ 2 +
          ‖d * s ^ 3 - z‖ ^ 2 := by simp [norm_pow]
      _ ≤ 4 * (2 * V * B ^ 2) * (2 * V * B ^ 2) ^ 2 + (2 * V * B ^ 3) ^ 2 := by
        gcongr
      _ = 32 * V ^ 3 * B ^ 6 + 4 * V ^ 2 * B ^ 6 := by ring
      _ ≤ 32 * V ^ 3 * B ^ 6 + 4 * V ^ 3 * B ^ 6 := by gcongr
      _ = 36 * V ^ 3 * B ^ 6 := by ring
  · calc
      _ ≤ ‖2 * (x + a * s) * (b * s ^ 2 - y)‖ + ‖d * s ^ 3 - z‖ := norm_add_le _ _
      _ = 2 * ‖x + a * s‖ * ‖b * s ^ 2 - y‖ + ‖d * s ^ 3 - z‖ := by simp
      _ ≤ 2 * (2 * V * B) * (2 * V * B ^ 2) + 2 * V * B ^ 3 := by gcongr
      _ = 8 * V ^ 2 * B ^ 3 + 2 * V * B ^ 3 := by ring
      _ ≤ 8 * V ^ 3 * B ^ 6 + 2 * V ^ 3 * B ^ 6 := by gcongr
      _ ≤ 36 * V ^ 3 * B ^ 6 := by nlinarith [mul_nonneg (pow_nonneg hV0 3) (pow_nonneg hB0 6)]

/-- The translated, denominator-cleared auxiliary sum has an entire extension
with an explicit disk bound once the four basic entire factors are supplied. -/
theorem solution
    (L : PeriodPair)
    (hZ : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (hrel : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    {ι : Type} [Fintype ι] (v : ℂ) (hv : v ∉ L.lattice)
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (D M : ℕ)
    (h₀ : ∀ i, l₀ i ≤ D) (h₂ : ∀ i, l₂ i ≤ M) (h₃ : ∀ i, l₃ i ≤ M) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        G z = σ z ^ (15 * M) * ∑ i, c i *
          clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) z) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D *
            (36 * (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
              ‖L.derivWeierstrassP v‖) ^ 3) ^ (15 * M) * B ^ (90 * M) := by
  classical
  let ψ : Fin 3 → ℂ → ℂ := ![
    fun z => 2 * (L.weierstrassP v * σ z ^ 2 - S 1 z),
    fun z => -4 * (S 1 z + L.weierstrassP v * σ z ^ 2) *
      (L.weierstrassP v * σ z ^ 2 - S 1 z) ^ 2 +
      (L.derivWeierstrassP v * σ z ^ 3 - S 2 z) ^ 2,
    fun z => 2 * (S 0 z + weierstrassZeta L v * σ z) *
      (L.weierstrassP v * σ z ^ 2 - S 1 z) +
      (L.derivWeierstrassP v * σ z ^ 3 - S 2 z)]
  let φ : Fin 3 → ℂ → ℂ := ![
    fun z => 2 * (L.weierstrassP v - L.weierstrassP z),
    fun z => -4 * (L.weierstrassP z + L.weierstrassP v) *
      (L.weierstrassP v - L.weierstrassP z) ^ 2 +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2,
    fun z => 2 * (weierstrassZeta L z + weierstrassZeta L v) *
      (L.weierstrassP v - L.weierstrassP z) +
      (L.derivWeierstrassP v - L.derivWeierstrassP z)]
  let w : Fin 3 → ℕ := ![2, 6, 3]
  let e (i : ι) : Fin 3 → ℕ := ![3 * M - 2 * l₂ i - l₃ i, l₂ i, l₃ i]
  have hψ (j : Fin 3) : AnalyticOnNhd ℂ (ψ j) univ := by
    intro z _
    have hs := hσ z trivial
    have hs0 := hS 0 z trivial
    have hs1 := hS 1 z trivial
    have hs2 := hS 2 z trivial
    fin_cases j <;> dsimp [ψ] <;> fun_prop
  have hrelation (z : ℂ) (hz : z ∉ L.lattice) (j : Fin 3) :
      ψ j z = σ z ^ w j * φ j z := by
    have h0 := hrel z hz 0
    have h1 := hrel z hz 1
    have h2 := hrel z hz 2
    simp [ellipticPoleCoordinates] at h0 h1 h2
    fin_cases j <;> simp [ψ, φ, w, h0, h1, h2] <;> ring
  have hw (j : Fin 3) : 1 ≤ w j := by fin_cases j <;> norm_num [w]
  have he (i : ι) : ∑ j, w j * e i j ≤ 15 * M := by
    simp [w, e, Fin.sum_univ_succ]
    have := h₂ i
    have := h₃ i
    omega
  obtain ⟨G, hG, hEq, hbound⟩ :=
    TranscendenceTheory.exists_entire_monomial_regularization (L.lattice : Set ℂ)ᶜ
      σ φ ψ hσ hψ w hw hrelation v c l₀ e D (15 * M) h₀ he
  refine ⟨G, hG, ?_, ?_⟩
  · intro z hz hzv
    rw [hEq z hz]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hZi := hZ z v hz hv hzv
    have hPi := hP z v hz hv hzv
    have hnum : 4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 =
        (2 * (L.weierstrassP v - L.weierstrassP z)) ^ 2 := by ring
    have hexp : 3 * M = (3 * M - 2 * l₂ i - l₃ i) + 2 * l₂ i + l₃ i := by
      have := h₂ i
      have := h₃ i
      omega
    dsimp only [φ, e]
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one]
    rw [show 2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) =
        2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) by
          linear_combination -hZi, ← hPi, hnum]
    unfold clearedAdditionMonomial
    conv_rhs => rw [hexp, pow_add, pow_add]
    simp only [mul_pow, ← pow_mul]
    ring
  · intro R B hB hbasic z hz
    let V := 1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ + ‖L.derivWeierstrassP v‖
    have hV : 1 ≤ V := by
      dsimp [V]
      linarith [norm_nonneg (weierstrassZeta L v), norm_nonneg (L.weierstrassP v),
        norm_nonneg (L.derivWeierstrassP v)]
    have hb' (z : ℂ) (hz : ‖z‖ ≤ R) :
        ‖σ z‖ ≤ 36 * V ^ 3 * B ^ 6 ∧ ∀ j, ‖ψ j z‖ ≤ 36 * V ^ 3 * B ^ 6 := by
      obtain ⟨hs, hA, hC, hD⟩ := cleared_factor_bounds (σ z) (S 0 z) (S 1 z) (S 2 z)
        (weierstrassZeta L v) (L.weierstrassP v) (L.derivWeierstrassP v) B V hB hV
        (hbasic z hz).1 ((hbasic z hz).2 0) ((hbasic z hz).2 1) ((hbasic z hz).2 2)
        (by dsimp [V]; linarith [norm_nonneg (L.weierstrassP v), norm_nonneg (L.derivWeierstrassP v)])
        (by dsimp [V]; linarith [norm_nonneg (weierstrassZeta L v), norm_nonneg (L.derivWeierstrassP v)])
        (by dsimp [V]; linarith [norm_nonneg (weierstrassZeta L v), norm_nonneg (L.weierstrassP v)])
      refine ⟨hs, ?_⟩
      intro j
      fin_cases j
      · exact hA
      · exact hC
      · exact hD
    have hbig : 1 ≤ 36 * V ^ 3 * B ^ 6 := by
      have := one_le_pow₀ hV (n := 3)
      have := one_le_pow₀ hB (n := 6)
      nlinarith
    have hh := hbound R (36 * V ^ 3 * B ^ 6) hbig hb' z hz
    simpa only [mul_pow, ← pow_mul, show 6 * (15 * M) = 90 * M by omega,
      mul_assoc, V] using hh

