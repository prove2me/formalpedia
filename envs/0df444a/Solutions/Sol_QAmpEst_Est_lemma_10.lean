-- Prove2me | solution 1 for QAmpEst.Est.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:26:00.985036+00:00
-- url     : https://prove2.me/submissions/6b19b648-02eb-416c-ad46-edbfec76334d

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

open scoped Real

namespace Aux_QAE_L10

lemma normSq_exp_sub_one (α : ℝ) :
    Complex.normSq (Complex.exp (↑α * Complex.I) - 1) = 4 * Real.sin (α / 2) ^ 2 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e : (↑(Real.cos α) + ↑(Real.sin α) * Complex.I - 1 : ℂ) =
      ↑(Real.cos α - 1) + ↑(Real.sin α) * Complex.I := by push_cast; ring
  rw [e, Complex.normSq_add_mul_I]
  have h1 := Real.cos_two_mul (α / 2)
  have h2 := Real.sin_sq_add_cos_sq (α / 2)
  have h3 := Real.sin_sq_add_cos_sq α
  rw [show 2 * (α / 2) = α by ring] at h1
  nlinarith

lemma sin_sq_shift (M : ℕ) (z : ℤ) (d : ℝ) :
    Real.sin ((M : ℝ) * |(z : ℝ) + d| * π) ^ 2 = Real.sin ((M : ℝ) * d * π) ^ 2 := by
  have key : Real.sin ((M : ℝ) * ((z : ℝ) + d) * π) ^ 2 = Real.sin ((M : ℝ) * d * π) ^ 2 := by
    have : (M : ℝ) * ((z : ℝ) + d) * π = (M : ℝ) * d * π + ((((M : ℤ) * z : ℤ)) : ℝ) * π := by
      push_cast; ring
    rw [this, Real.sin_add_int_mul_pi, mul_pow]
    have : ((-1 : ℝ) ^ ((M : ℤ) * z)) ^ 2 = 1 := by
      rw [← sq_abs, abs_zpow, abs_neg, abs_one, one_zpow, one_pow]
    rw [this, one_mul]
  rcases abs_choice ((z : ℝ) + d) with h | h
  · rw [h, key]
  · rw [h, show (M : ℝ) * -((z : ℝ) + d) * π = -((M : ℝ) * ((z : ℝ) + d) * π) by ring,
      Real.sin_neg, neg_sq, key]

end Aux_QAE_L10

open QAmpEst.Est Aux_QAE_L10 in
theorem solution (M : ℕ) (hM : 0 < M) (ω0 ω1 : ℝ) (hω0 : 0 ≤ ω0) (hω0' : ω0 < 1)
    (hω1 : 0 ≤ ω1) (hω1' : ω1 < 1) :
    let Δ := circDist ω0 ω1
    let ip := ∑ y, star (stateS M ω0 y) * stateS M ω1 y
    (Δ = 0 → Complex.normSq ip = 1) ∧
      (Δ ≠ 0 → Complex.normSq ip =
        Real.sin ((M : ℝ) * Δ * π) ^ 2 / ((M : ℝ) ^ 2 * Real.sin (Δ * π) ^ 2)) := by
  intro Δ ip
  set d := ω1 - ω0 with hd
  have hd1 : -1 < d := by linarith
  have hd2 : d < 1 := by linarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- the circular distance is attained
  have hbdd : BddBelow (Set.range fun z : ℤ => |(z : ℝ) + ω1 - ω0|) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact abs_nonneg _⟩
  have hform : ∀ z : ℤ, |(z : ℝ) + ω1 - ω0| = |(z : ℝ) + d| := fun z => by rw [hd]; ring_nf
  have hattain : ∃ z₀ : ℤ, Δ = |(z₀ : ℝ) + d| := by
    set m := min (min |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d|) |((1 : ℤ) : ℝ) + d| with hm
    have hm0 : m ≤ |d| := by
      have := min_le_left (min |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d|) |((1 : ℤ) : ℝ) + d|
      have := min_le_right |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d|
      simp only [Int.cast_zero, zero_add] at *
      linarith
    have hΔm : Δ = m := by
      apply le_antisymm
      · show circDist ω0 ω1 ≤ m
        unfold circDist
        rcases min_choice (min |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d|) |((1 : ℤ) : ℝ) + d|
          with h | h <;> rw [hm, h]
        · rcases min_choice |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d| with h' | h' <;> rw [h']
          · rw [← hform]; exact ciInf_le hbdd (-1)
          · rw [← hform]; exact ciInf_le hbdd 0
        · rw [← hform]; exact ciInf_le hbdd 1
      · show m ≤ circDist ω0 ω1
        unfold circDist
        apply le_ciInf
        intro z
        rw [hform]
        have hz : z ≤ -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ 2 ≤ z := by omega
        rcases hz with hz | rfl | rfl | rfl | hz
        · have : (z : ℝ) ≤ -2 := by exact_mod_cast hz
          have : 1 ≤ |(z : ℝ) + d| := by rw [abs_of_neg (by linarith)]; linarith
          have : |d| < 1 := abs_lt.mpr ⟨hd1, hd2⟩
          linarith
        · exact (min_le_left _ _).trans (min_le_left _ _)
        · exact (min_le_left _ _).trans (min_le_right _ _)
        · exact min_le_right _ _
        · have : (2 : ℝ) ≤ z := by exact_mod_cast hz
          have : 1 ≤ |(z : ℝ) + d| := by rw [abs_of_pos (by linarith)]; linarith
          have : |d| < 1 := abs_lt.mpr ⟨hd1, hd2⟩
          linarith
    rw [hΔm]
    rcases min_choice (min |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d|) |((1 : ℤ) : ℝ) + d|
      with h | h
    · rcases min_choice |((-1 : ℤ) : ℝ) + d| |((0 : ℤ) : ℝ) + d| with h' | h'
      · exact ⟨-1, by rw [hm, h, h']⟩
      · exact ⟨0, by rw [hm, h, h']⟩
    · exact ⟨1, by rw [hm, h]⟩
  obtain ⟨z₀, hz₀⟩ := hattain
  -- the inner product as a geometric sum
  set r := Complex.exp (↑(2 * π * d) * Complex.I) with hr
  have hterm : ∀ y : Fin M, star (stateS M ω0 y) * stateS M ω1 y = r ^ (y : ℕ) / M := by
    intro y
    unfold stateS
    have hsq : ((Real.sqrt M : ℝ) : ℂ) * ((Real.sqrt M : ℝ) : ℂ) = (M : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg M), Complex.ofReal_natCast]
    have hconj : star (Complex.exp (2 * ↑π * Complex.I * ↑ω0 * ↑(y : ℕ))) =
        Complex.exp (-(2 * ↑π * Complex.I * ↑ω0 * ↑(y : ℕ))) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_I, map_natCast, map_ofNat]
      ring
    rw [star_div₀, hconj, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, hsq,
      ← Complex.exp_add, hr, ← Complex.exp_nat_mul]
    congr 2
    rw [hd]
    push_cast
    ring
  have hip : ip = (∑ k ∈ Finset.range M, r ^ k) / M := by
    show ∑ y, star (stateS M ω0 y) * stateS M ω1 y = _
    simp only [hterm]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun k => r ^ k)]
  have hd0iff : d = 0 → Complex.normSq ip = 1 := by
    intro h0
    have hr1 : r = 1 := by rw [hr, h0]; simp
    rw [hip, hr1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [div_self (by exact_mod_cast hM.ne')]
    simp
  constructor
  · intro hΔ
    apply hd0iff
    rw [hΔ] at hz₀
    have h1 : (z₀ : ℝ) + d = 0 := abs_eq_zero.mp hz₀.symm
    have h2 : (z₀ : ℝ) = -d := by linarith
    have h3 : z₀ = 0 := by
      have h4r : (-1 : ℝ) < z₀ := by linarith
      have h5r : (z₀ : ℝ) < 1 := by linarith
      have h4 : -1 < z₀ := by exact_mod_cast h4r
      have h5 : z₀ < 1 := by exact_mod_cast h5r
      omega
    rw [h3] at h2; simp at h2; linarith
  · intro hΔ
    have hdne : d ≠ 0 := by
      intro h0
      apply hΔ
      apply le_antisymm
      · show circDist ω0 ω1 ≤ 0
        unfold circDist
        have := ciInf_le hbdd 0
        rw [hform, Int.cast_zero, zero_add, h0, abs_zero] at this
        exact this
      · show 0 ≤ circDist ω0 ω1
        unfold circDist
        exact le_ciInf (fun z => abs_nonneg _)
    have hsin : Real.sin (d * π) ≠ 0 := by
      intro hs
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
      have hnd : (n : ℝ) = d := by
        have := Real.pi_pos
        field_simp at hn
        linarith
      have h4 : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
      have h5 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
      have hn0 : n = 0 := by omega
      apply hdne
      rw [← hnd, hn0, Int.cast_zero]
    have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hre : 2 * π * d = n * (2 * π) := by
        have := congrArg Complex.im hn
        simpa using this
      have hdn : d = n := by
        have := Real.pi_pos
        nlinarith
      have h4 : -1 < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
      have h5 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
      have hn0 : n = 0 := by omega
      apply hdne
      rw [hdn, hn0, Int.cast_zero]
    have hgeom : ∑ k ∈ Finset.range M, r ^ k = (r ^ M - 1) / (r - 1) := geom_sum_eq hr1 M
    have hrM : r ^ M = Complex.exp (↑((M : ℝ) * (2 * π * d)) * Complex.I) := by
      rw [hr, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hN1 := normSq_exp_sub_one ((M : ℝ) * (2 * π * d))
    have hN2 := normSq_exp_sub_one (2 * π * d)
    rw [← hrM] at hN1
    rw [← hr] at hN2
    rw [hip, hgeom, Complex.normSq_div, Complex.normSq_div, hN1, hN2, Complex.normSq_natCast]
    rw [hz₀, sin_sq_shift M z₀ d]
    have hs1 : Real.sin (|(z₀ : ℝ) + d| * π) ^ 2 = Real.sin (d * π) ^ 2 := by
      have := sin_sq_shift 1 z₀ d
      simpa using this
    rw [hs1]
    have e1 : (M : ℝ) * (2 * π * d) / 2 = (M : ℝ) * d * π := by ring
    have e2 : 2 * π * d / 2 = d * π := by ring
    rw [e1, e2]
    have hsin2 : Real.sin (d * π) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
    field_simp
