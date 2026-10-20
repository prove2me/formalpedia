-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.tracePolygonObstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:36:36.730305+00:00
-- url     : https://prove2.me/submissions/5b2f5079-f0ce-454d-9c28-f629ea75837e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_trace_kraus {K : Type*} [Fintype K] {d : ℕ} (E : K → Mat d)
    (hK : IsKrausFamily E) (X : Mat d) : (krausApply E X).trace = X.trace := by
  simp only [krausApply, Matrix.trace_sum]
  have : ∀ j, (E j * X * (E j)ᴴ).trace = ((E j)ᴴ * E j * X).trace := fun j => by
    rw [Matrix.trace_mul_cycle]
  simp only [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show ∑ j, (E j)ᴴ * E j = 1 from hK, Matrix.one_mul]

theorem g52c_trace_channel {d : ℕ} (Phi : Map d) (hPhi : IsChannel Phi) (X : Mat d) :
    (Phi X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := hPhi
  rw [hE]; exact g52c_trace_kraus E hK X

theorem g52c_diag_sum_zero {d : ℕ} (Phi : Map d) (hTP : ∀ X, (Phi X).trace = X.trace)
    (i j : Fin d) (hij : i ≠ j) : ∑ r, Phi (matrixUnit i j) r r = 0 := by
  have := hTP (matrixUnit i j)
  simp only [Matrix.trace, Matrix.diag] at this
  rw [this]
  apply Finset.sum_eq_zero
  intro r _
  simp only [matrixUnit, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij rfl

theorem g52c_gibbs_sum {b : ℕ} (hb : 0 < b) (e : Fin b → ℝ) (beta : ℝ) :
    ∑ m, gibbsWeight e beta m = 1 := by
  simp only [gibbsWeight]
  rw [← Finset.sum_div, div_self]
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  exact (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem g52c_thermal_kraus {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : IsKrausFamily (thermalKraus D) := by
  have hU : star (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) * D.U = 1 :=
    Unitary.star_mul_self_of_mem D.U.2
  rw [Matrix.star_eq_conjTranspose] at hU
  have hUe : ∀ (i j : Fin d) (m : Fin b),
      ∑ r, ∑ n, star ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (i, m)) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (j, m) =
        if i = j then 1 else 0 := by
    intro i j m
    have := congrFun (congrFun hU (i, m)) (j, m)
    rw [Matrix.mul_apply, Fintype.sum_prod_type] at this
    simp only [Matrix.conjTranspose_apply] at this
    rw [this, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  unfold IsKrausFamily
  ext i j
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, thermalKraus, star_mul',
    Complex.star_def, Complex.conj_ofReal]
  have hw : ∀ m : Fin b, ((Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ)) *
      (Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) = (gibbsWeight D.bathEnergy beta m : ℂ) := by
    intro m
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
    simp only [gibbsWeight]
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le))
  have step : ∀ m : Fin b, ∑ n, ∑ r,
      (Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) *
        (starRingEnd ℂ) ((D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (i, m)) *
      ((Real.sqrt (gibbsWeight D.bathEnergy beta m) : ℂ) *
        (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, n) (j, m)) =
      (gibbsWeight D.bathEnergy beta m : ℂ) * (if i = j then 1 else 0) := by
    intro m
    rw [← hUe i j m, Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [← hw m]; simp only [Complex.star_def]; ring
  rw [Finset.sum_congr rfl (fun m _ => step m), ← Finset.sum_mul]
  have hs : ∑ m, (gibbsWeight D.bathEnergy beta m : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, g52c_gibbs_sum D.bathPositive, Complex.ofReal_one]
  rw [hs, one_mul, Matrix.one_apply]

theorem g52c_polygon {d : ℕ} (Phi : Map d) (hTP : ∀ X, (Phi X).trace = X.trace)
    (i j : Fin d) (hij : i ≠ j) (s : Fin d → ℝ) (r0 : Fin d)
    (hstrict : (∑ r ∈ Finset.univ.erase r0, s r) < s r0)
    (hn : ∀ r, ‖Phi (matrixUnit i j) r r‖ = s r) : False := by
  have hsum := g52c_diag_sum_zero Phi hTP i j hij
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r0)] at hsum
  have heq : Phi (matrixUnit i j) r0 r0 = -∑ r ∈ Finset.univ.erase r0, Phi (matrixUnit i j) r r := by
    linear_combination hsum
  have : s r0 ≤ ∑ r ∈ Finset.univ.erase r0, s r := by
    rw [← hn r0, heq, norm_neg]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun r _ => hn r)))
  linarith

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d : ℕ} (hd : 0 < d) (P Q : Fin d → ℝ)
    (hP : ∀ r, 0 ≤ P r) (hQ : ∀ r, 0 ≤ Q r)
    (hPsum : ∑ r, P r = 1) (hQsum : ∑ r, Q r = 1) (i j : Fin d) (hij : i ≠ j)
    (r0 : Fin d) (hstrict : (∑ r ∈ Finset.univ.erase r0, Real.sqrt (P r * Q r)) <
      Real.sqrt (P r0 * Q r0)) :
    (¬ ∃ Phi : Map d, IsChannel Phi ∧
      (∀ r, population Phi r i = P r ∧ population Phi r j = Q r) ∧
      ∀ r, ‖Phi (matrixUnit i j) r r‖ = Real.sqrt (P r * Q r)) ∧
    (∀ (E : Fin d → ℝ) (beta : ℝ), ¬ ∃ Phi : Map d, IsFiniteThermal E beta Phi ∧
      (∀ r, population Phi r i = P r ∧ population Phi r j = Q r) ∧
      ∀ r, ‖Phi (matrixUnit i j) r r‖ = Real.sqrt (P r * Q r)) := by
  constructor
  · rintro ⟨Phi, hPhi, -, hn⟩
    exact g52c_polygon Phi (g52c_trace_channel Phi hPhi) i j hij _ r0 hstrict hn
  · rintro E beta ⟨Phi, ⟨b, D, hD⟩, -, hn⟩
    have hTP : ∀ X, (Phi X).trace = X.trace := by
      intro X
      rw [hD X]
      exact g52c_trace_kraus (thermalKraus D) (g52c_thermal_kraus D) X
    exact g52c_polygon Phi hTP i j hij _ r0 hstrict hn
