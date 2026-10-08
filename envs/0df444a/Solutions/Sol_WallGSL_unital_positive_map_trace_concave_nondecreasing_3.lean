-- Prove2me | solution 3 for WallGSL.unital_positive_map_trace_concave_nondecreasing
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:22:32.373329+00:00
-- url     : https://prove2.me/submissions/a0d3f5e8-19ed-4bdd-b08e-af3e0dabbc41

import Mathlib

open Matrix
open scoped ComplexOrder

/-- Corollary 4 (appendix) of Wall (2013), with the convexity condition read as concavity
(see the formalization note): for every function `f` concave on `[0, ∞)`, the quantity
`tr f(ρ) = ∑ⱼ f(pⱼ)` does not decrease under a trace-preserving, identity-preserving,
positive linear map `T`. -/
theorem solution
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hT_pos : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → (T A).PosSemidef)
    (hT_trace : ∀ A : Matrix (Fin n) (Fin n) ℂ, (T A).trace = A.trace)
    (hT_one : T 1 = 1)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) :
    ∑ j, f (hρ.isHermitian.eigenvalues j) ≤ ∑ j, f ((hT_pos ρ hρ).isHermitian.eigenvalues j) := by
  set hA := hρ.isHermitian
  set hB := (hT_pos ρ hρ).isHermitian
  set p := hA.eigenvalues
  set q := hB.eigenvalues
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set V : Matrix (Fin n) (Fin n) ℂ := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hV : V * star V = 1 := Unitary.coe_mul_star_self _
  let E : Fin n → Matrix (Fin n) (Fin n) ℂ := fun j => U * diagonal (Pi.single j 1) * star U
  have hρE : ρ = ∑ j, (p j : ℂ) • E j := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    have : ∑ j, (p j : ℂ) • E j = U * (∑ j, (p j : ℂ) • diagonal (Pi.single j 1)) * star U := by
      simp only [E, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    congr 2
    ext a b
    simp [diagonal, Matrix.sum_apply, Pi.single_apply]
    split_ifs <;> simp_all <;> rfl
  have hE1 : ∑ j, E j = 1 := by
    simp only [E]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    have : ∑ j : Fin n, diagonal (Pi.single j (1:ℂ)) = 1 := by
      ext a b
      simp [diagonal, Matrix.sum_apply, Pi.single_apply, Matrix.one_apply]
    rw [this, mul_one, hU]
  have hEpsd : ∀ j, (E j).PosSemidef := by
    intro j
    have h0 : (diagonal (Pi.single j (1:ℂ))).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i; by_cases h : i = j <;> simp [Pi.single_apply, h]
    simpa [E, star_eq_conjTranspose] using h0.mul_mul_conjTranspose_same U
  have hEtr : ∀ j, (E j).trace = 1 := by
    intro j
    simp only [E]
    rw [trace_mul_comm, ← Matrix.mul_assoc]
    rw [show star U * U = 1 from Unitary.coe_star_mul_self _, Matrix.one_mul]
    simp [trace, diagonal, Pi.single_apply]
  let D : Fin n → Fin n → ℝ := fun i j => ((star V * T (E j) * V) i i).re
  have hD0 : ∀ i j, 0 ≤ D i j := by
    intro i j
    have := ((hT_pos _ (hEpsd j)).conjTranspose_mul_mul_same V).diag_nonneg (i := i)
    rw [← star_eq_conjTranspose] at this
    exact (Complex.nonneg_iff.mp this).1
  have hrow : ∀ i, ∑ j, D i j = 1 := by
    intro i
    simp only [D]
    have h1 : ∑ j, star V * T (E j) * V = 1 := by
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← map_sum, hE1, hT_one, Matrix.mul_one]
      exact Unitary.coe_star_mul_self _
    rw [← Complex.re_sum, ← Matrix.sum_apply i i Finset.univ (fun j => star V * T (E j) * V), h1]
    simp
  have hcol : ∀ j, ∑ i, D i j = 1 := by
    intro j
    simp only [D]
    rw [← Complex.re_sum]
    change (trace (star V * T (E j) * V)).re = 1
    rw [trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, hT_trace, hEtr]
    simp
  have hq : ∀ i, q i = ∑ j, D i j * p j := by
    intro i
    have h := congrArg (fun M => M i i) hB.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    have h2 : ((star V * T ρ * V) i i).re = q i := by
      change ((star V * T ρ * V) i i).re = hB.eigenvalues i
      rw [h]; simp
    rw [← h2]
    conv_lhs => rw [hρE]
    simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, Complex.re_sum, smul_eq_mul,
      Complex.re_ofReal_mul, D]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hp0 : ∀ j, 0 ≤ p j := hρ.eigenvalues_nonneg
  calc ∑ j, f (p j) = ∑ j, (∑ i, D i j) * f (p j) := by simp [hcol]
    _ = ∑ i, ∑ j, D i j • f (p j) := by
        simp_rw [Finset.sum_mul, smul_eq_mul]; exact Finset.sum_comm
    _ ≤ ∑ i, f (∑ j, D i j • p j) := by
        gcongr with i
        exact hf.le_map_sum (fun j _ => hD0 i j) (hrow i) (fun j _ => hp0 j)
    _ = ∑ i, f (q i) := by simp_rw [hq, smul_eq_mul]
