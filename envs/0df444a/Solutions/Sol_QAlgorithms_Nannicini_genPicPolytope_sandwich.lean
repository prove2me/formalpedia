-- Prove2me | solution 1 for QAlgorithms.Nannicini.genPicPolytope_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:28:17.458518+00:00
-- url     : https://prove2.me/submissions/a82e8717-0ad9-4bdb-8626-394ea52fc4e6

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open QAlgorithms QAlgorithms.SDP
open scoped ComplexOrder

private lemma trace_combination {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → ℝ) :
    ((∑ j, (y j : ℂ) • A j - C) * Z).trace.re =
      ∑ j, (A j * Z).trace.re * y j - (C * Z).trace.re := by
  simp [Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_sub,
    Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re, mul_comm]

private lemma weighted_error {m : ℕ} (a atil y : Fin m → ℝ) (θ r : ℝ)
    (hθ : 0 ≤ θ) (hy : ∀ j, 0 ≤ y j) (hyr : ∑ j, y j ≤ r)
    (ha : ∀ j, |a j - atil j| ≤ θ) :
    |∑ j, a j * y j - ∑ j, atil j * y j| ≤ θ * r := by
  calc
    _ = |∑ j, (a j - atil j) * y j| := by simp_rw [sub_mul]; rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j, |(a j - atil j) * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, θ * y j := Finset.sum_le_sum fun j _ => by
      rw [abs_mul, abs_of_nonneg (hy j)]
      exact mul_le_mul_of_nonneg_right (ha j) (hy j)
    _ = θ * ∑ j, y j := (Finset.mul_sum _ _ _).symm
    _ ≤ θ * r := mul_le_mul_of_nonneg_left hyr hθ

theorem solution {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R r : ℝ)
    (_hAherm : ∀ j, (A j).IsHermitian) (_hCherm : C.IsHermitian)
    (_hA1 : A ⟨0, hm⟩ = 1) (_hb1 : b ⟨0, hm⟩ = R) (_hR : 0 < R) (_hC : specNorm C ≤ 1)
    (hr : 1 ≤ r) (_hopt : ∃ y : Fin m → ℝ, IsDualOptimal A C b y ∧ ∑ j, |y j| ≤ r)
    (γ : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) (hXR : X.trace.re ≤ R)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ = (X.trace)⁻¹ • X)
    (θ : ℝ) (hθ : 0 ≤ θ) (atil : Fin m → ℝ) (ctil : ℝ)
    (hc : |(C * ρ).trace.re - ctil| ≤ θ) (ha : ∀ j, |(A j * ρ).trace.re - atil j| ≤ θ) :
    picPolytope A b C γ 0 X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r} ⊆
        genPicPolytope b γ r atil (ctil - (r + 1) * θ) ∧
      genPicPolytope b γ r atil (ctil - (r + 1) * θ) ⊆
        picPolytope A b C γ (4 * R * r * θ) X ∩ {y : Fin m → ℝ | ∑ j, |y j| ≤ r}  := by
  classical
  have ht := Complex.nonneg_iff.mp hX.trace_nonneg
  have htrace : X.trace = (X.trace.re : ℂ) := by
    apply Complex.ext <;> simp [ht.2.symm]
  have hscale (Z : Matrix (Fin n) (Fin n) ℂ) :
      (Z * ρ).trace.re = (X.trace.re)⁻¹ * (Z * X).trace.re := by
    rw [hρ, htrace]
    simp [Matrix.trace_smul, Complex.mul_re]
  have hreconstruct : X = (X.trace.re : ℂ) • ρ := by
    by_cases hz : X.trace = 0
    · have hx := hX.trace_eq_zero_iff.mp hz
      simp [hx, hρ]
    · rw [hρ, ← htrace, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have hback (Z : Matrix (Fin n) (Fin n) ℂ) :
      (Z * X).trace.re = X.trace.re * (Z * ρ).trace.re := by
    conv_lhs => rw [hreconstruct]
    simp [Matrix.trace_smul, Complex.mul_re]
  constructor
  · intro y hy
    rcases hy with ⟨⟨hbudget, hpos, hy⟩, hnorm⟩
    have hyr : ∑ j, y j ≤ r := by
      simpa only [Set.mem_ofPred_eq, abs_of_nonneg (hy _)] using hnorm
    have he := abs_le.mp (weighted_error (fun j => (A j * ρ).trace.re) atil y θ r hθ hy hyr ha)
    have hp : 0 ≤ ∑ j, (A j * ρ).trace.re * y j - (C * ρ).trace.re := by
      rw [← trace_combination, hscale]
      exact mul_nonneg (inv_nonneg.mpr ht.1) (by simpa using hpos)
    exact ⟨hbudget, hyr, by have hh := abs_le.mp hc; nlinarith, hy⟩
  · intro y hy
    rcases hy with ⟨hbudget, hyr, happrox, hy⟩
    have he := abs_le.mp (weighted_error (fun j => (A j * ρ).trace.re) atil y θ r hθ hy hyr ha)
    have hp : -(4 * r * θ) ≤ ∑ j, (A j * ρ).trace.re * y j - (C * ρ).trace.re := by
      have hh := abs_le.mp hc
      have hh' := mul_nonneg (sub_nonneg.mpr hr) hθ
      nlinarith
    refine ⟨⟨hbudget, ?_, hy⟩, ?_⟩
    · rw [hback, trace_combination]
      have hmul := mul_le_mul_of_nonneg_left hp ht.1
      have hrθ : 0 ≤ 4 * r * θ := by positivity
      have hbound := mul_le_mul_of_nonneg_right hXR hrθ
      nlinarith
    · simpa only [Set.mem_ofPred_eq, abs_of_nonneg (hy _)] using hyr
