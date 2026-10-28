-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.eq_64_65
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:59:30.031493+00:00
-- url     : https://prove2.me/submissions/7e379e9a-304f-428e-b5b7-eb3142deb09d

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace Aux_QSVT_6465

open Complex

lemma pow_eig {N : Type} [Fintype N] [DecidableEq N] (M : Matrix N N ℂ) (u : N → ℂ) (c : ℂ)
    (h : M.mulVec u = c • u) : ∀ k : ℕ, (M ^ k).mulVec u = c ^ k • u := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

lemma scal1 (x : ℝ) :
    (1 / 2 : ℂ) * (1 + exp (2 * Real.pi * I * x)) =
      (Real.cos (Real.pi * x) : ℂ) * exp (Real.pi * I * x) := by
  rw [ofReal_cos, Complex.cos]
  push_cast
  have h1 : exp (↑Real.pi * ↑x * I) = exp (Real.pi * I * x) := by congr 1; ring
  have h2 : exp (2 * Real.pi * I * x) = exp (Real.pi * I * x) * exp (Real.pi * I * x) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h3 : exp (-(↑Real.pi * ↑x) * I) * exp (Real.pi * I * x) = 1 := by
    rw [← Complex.exp_add]
    have : -(↑Real.pi * ↑x) * I + Real.pi * I * x = 0 := by ring
    rw [this, Complex.exp_zero]
  rw [h1, h2]
  linear_combination (-1 / 2 : ℂ) * h3

lemma scal2 (x : ℝ) :
    (1 / 2 : ℂ) * (1 + exp (-2 * Real.pi * I * x)) * exp (Real.pi * I * x) =
      (Real.cos (Real.pi * x) : ℂ) := by
  rw [ofReal_cos, Complex.cos]
  push_cast
  have h1 : exp (↑Real.pi * ↑x * I) = exp (Real.pi * I * x) := by congr 1; ring
  have h2 : exp (-2 * Real.pi * I * x) * exp (Real.pi * I * x) =
      exp (-(↑Real.pi * ↑x) * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h1]
  linear_combination (1 / 2 : ℂ) * h2

end Aux_QSVT_6465

open QSVTPhaseEst.BitSearch Complex in
theorem solution {N : Type} [Fintype N] [DecidableEq N] (U : Matrix N N ℂ)
    (hU : U ∈ Matrix.unitaryGroup N ℂ) (u : N → ℂ) (φ θ : ℝ) (j : ℕ)
    (hUu : U.mulVec u = Complex.exp (2 * Real.pi * Complex.I * φ) • u) :
    let A : Matrix N N ℂ :=
      (1 / 2 : ℂ) • (1 + Complex.exp (-2 * Real.pi * Complex.I * θ) • U ^ (2 ^ j))
    let x : ℝ := (2 : ℝ) ^ j * φ - θ
    A.mulVec u = ((Real.cos (Real.pi * x) : ℂ) * Complex.exp (Real.pi * Complex.I * x)) • u ∧
    A.conjTranspose.mulVec (Complex.exp (Real.pi * Complex.I * x) • u) =
      (Real.cos (Real.pi * x) : ℂ) • u ∧
    sigma φ j θ = |Real.cos (Real.pi * (Int.fract ((2 : ℝ) ^ j * φ) - θ))| := by
  intro A x
  -- eigen-relation for the adjoint
  have hstar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUh : U.conjTranspose.mulVec u = exp (-2 * Real.pi * I * φ) • u := by
    have h1 : U.conjTranspose.mulVec (U.mulVec u) = u := by
      rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hstar, Matrix.one_mulVec]
    rw [hUu, Matrix.mulVec_smul] at h1
    have hne : exp (2 * Real.pi * I * φ) ≠ 0 := Complex.exp_ne_zero _
    have h2 : exp (-2 * Real.pi * I * φ) * exp (2 * Real.pi * I * φ) = 1 := by
      rw [← Complex.exp_add]
      have : -2 * Real.pi * I * φ + 2 * Real.pi * I * φ = 0 := by ring
      rw [this, Complex.exp_zero]
    calc U.conjTranspose.mulVec u
        = (exp (-2 * Real.pi * I * φ) * exp (2 * Real.pi * I * φ)) •
            U.conjTranspose.mulVec u := by rw [h2, one_smul]
      _ = exp (-2 * Real.pi * I * φ) • u := by rw [← smul_smul, h1]
  have hp1 := Aux_QSVT_6465.pow_eig U u _ hUu (2 ^ j)
  have hp2 := Aux_QSVT_6465.pow_eig U.conjTranspose u _ hUh (2 ^ j)
  have hxc : ((x : ℝ) : ℂ) = (2 : ℂ) ^ j * φ - θ := by
    simp only [x]; push_cast; ring
  have e1 : exp (-2 * Real.pi * I * θ) * exp (2 * Real.pi * I * φ) ^ (2 ^ j) =
      exp (2 * Real.pi * I * x) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hxc]
    congr 1
    push_cast
    ring
  have e2 : exp (2 * Real.pi * I * θ) * exp (-2 * Real.pi * I * φ) ^ (2 ^ j) =
      exp (-2 * Real.pi * I * x) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hxc]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hs := Aux_QSVT_6465.scal1 x
    rw [← e1] at hs
    simp only [A]
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hp1]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (u i) * hs
  · have hs := Aux_QSVT_6465.scal2 x
    rw [← e2] at hs
    have hA : A.conjTranspose = (1 / 2 : ℂ) •
        (1 + exp (2 * Real.pi * I * θ) • U.conjTranspose ^ (2 ^ j)) := by
      simp only [A]
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_pow]
      congr 1
      · simp
      · congr 2
        have hc : (starRingEnd ℂ) (-2 * ↑Real.pi * I * ↑θ) = 2 * Real.pi * I * θ := by
          rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
            map_neg, map_ofNat]
          ring
        rw [Complex.star_def, ← Complex.exp_conj, hc]
    rw [hA, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, hp2]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (u i) * hs
  · unfold sigma
    have hfl := Int.fract_add_floor ((2 : ℝ) ^ j * φ)
    have : Real.pi * ((2 : ℝ) ^ j * φ - θ) =
        Real.pi * (Int.fract ((2 : ℝ) ^ j * φ) - θ) + (⌊(2 : ℝ) ^ j * φ⌋ : ℝ) * Real.pi := by
      linear_combination (-Real.pi) * hfl
    rw [this, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
