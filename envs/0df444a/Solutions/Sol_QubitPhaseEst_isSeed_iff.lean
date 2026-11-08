-- Prove2me | solution 1 for QubitPhaseEst.isSeed_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:07:45.599342+00:00
-- url     : https://prove2.me/submissions/33b1305c-9a61-4cca-a5cf-278c22280ca7

import Mathlib
import Definitions.Def_QubitPhaseEst_IsSeed

open scoped Matrix ComplexOrder

namespace Aux_QPEseed

open QubitPhaseEst

theorem mz_eq {N : ℕ} (x : Qb N) :
    mz x = ((Finset.univ.filter (fun k => x k = 0)).card : ℝ) - N / 2 := by
  unfold mz
  have : ∀ k, (if x k = 0 then (1 / 2 : ℝ) else -1 / 2) = (if x k = 0 then 1 else 0) - 1 / 2 := by
    intro k; split_ifs <;> norm_num
  simp only [this]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem int_exp (k : ℤ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((-(k : ℂ) * Complex.I) * (φ : ℂ))) =
      if k = 0 then 2 * (Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hc : (-(k : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · simp [hk]
      · exact Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (-(k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem entry {N : ℕ} (ξ : Matrix (Qb N) (Qb N) ℂ) (x y : Qb N) (φ : ℝ) (k : ℤ)
    (hk : mz x - mz y = (k : ℝ)) :
    (phaseShift N φ * ξ * (phaseShift N φ)ᴴ) x y =
      ξ x y * Complex.exp ((-(k : ℂ) * Complex.I) * (φ : ℂ)) := by
  unfold phaseShift
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hstar : (star fun x : Qb N => Complex.exp (-((φ : ℂ) * (mz x : ℂ)) * Complex.I)) y =
      Complex.exp (((φ : ℂ) * (mz y : ℂ)) * Complex.I) := by
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  rw [hstar]
  have hkC : (mz x : ℂ) - (mz y : ℂ) = (k : ℂ) := by
    rw [← Complex.ofReal_sub, hk]; simp
  calc Complex.exp (-((φ : ℂ) * (mz x : ℂ)) * Complex.I) * ξ x y *
        Complex.exp (((φ : ℂ) * (mz y : ℂ)) * Complex.I)
      = ξ x y * (Complex.exp (-((φ : ℂ) * (mz x : ℂ)) * Complex.I) *
          Complex.exp (((φ : ℂ) * (mz y : ℂ)) * Complex.I)) := by ring
    _ = ξ x y * Complex.exp (-((φ : ℂ) * (mz x : ℂ)) * Complex.I +
          ((φ : ℂ) * (mz y : ℂ)) * Complex.I) := by rw [Complex.exp_add]
    _ = ξ x y * Complex.exp ((-(k : ℂ) * Complex.I) * (φ : ℂ)) := by
        congr 2
        rw [← hkC]
        ring

theorem key {N : ℕ} (ξ : Matrix (Qb N) (Qb N) ℂ) (x y : Qb N) :
    (1 / (2 * (Real.pi : ℂ))) *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), (phaseShift N φ * ξ * (phaseShift N φ)ᴴ) x y =
      if mz x = mz y then ξ x y else 0 := by
  set k : ℤ := ((Finset.univ.filter (fun j => x j = 0)).card : ℤ) -
    ((Finset.univ.filter (fun j => y j = 0)).card : ℤ) with hkdef
  have hk : mz x - mz y = (k : ℝ) := by
    rw [mz_eq, mz_eq, hkdef]; push_cast; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [entry ξ x y _ k hk]
  rw [intervalIntegral.integral_const_mul, int_exp]
  by_cases h : mz x = mz y
  · have : k = 0 := by
      have : (k : ℝ) = 0 := by rw [← hk, h, sub_self]
      exact_mod_cast this
    rw [if_pos this, if_pos h]
    field_simp
  · have : k ≠ 0 := by
      intro h0
      apply h
      have : mz x - mz y = 0 := by rw [hk, h0]; simp
      linarith
    rw [if_neg this, if_neg h]
    simp

end Aux_QPEseed

open QubitPhaseEst Aux_QPEseed in
theorem solution {N : ℕ} (ξ : Matrix (Qb N) (Qb N) ℂ) :
    IsSeed ξ ↔ ξ.PosSemidef ∧ ∀ x y : Qb N, mz x = mz y → ξ x y = if x = y then 1 else 0 := by
  unfold IsSeed
  simp only [key]
  constructor
  · rintro ⟨hpsd, h⟩
    refine ⟨hpsd, fun x y hxy => ?_⟩
    have := h x y
    rw [if_pos hxy, Matrix.one_apply] at this
    exact this
  · rintro ⟨hpsd, h⟩
    refine ⟨hpsd, fun x y => ?_⟩
    rw [Matrix.one_apply]
    by_cases hxy : mz x = mz y
    · rw [if_pos hxy]; exact h x y hxy
    · rw [if_neg hxy]
      have : x ≠ y := fun e => hxy (by rw [e])
      rw [if_neg this]
