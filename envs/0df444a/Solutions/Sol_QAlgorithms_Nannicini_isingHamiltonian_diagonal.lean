-- Prove2me | solution 1 for QAlgorithms.Nannicini.isingHamiltonian_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:13:06.079772+00:00
-- url     : https://prove2.me/submissions/bf505245-b4a5-42d8-836a-53924cd7ba21

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open QAlgorithms QAlgorithms.Stabilizer

private lemma pauliZ_wire_diagonal {n : ℕ} (j : Fin n) :
    CliffordOp.mat (CliffordOp.pauli j Pauli.Z) =
      Matrix.diagonal (fun x : Qubits n => ((1 - 2 * boolPoint x j : ℝ) : ℂ)) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    change (if ∀ k : Fin n, k ∉ Set.range (wire1 j) → x k = x k then
      pauliZ (x j) (x j) else 0) = _
    simp only [implies_true, ite_true, pauliZ,
      Matrix.diagonal_apply_eq]
    cases hb : x j <;> norm_num [boolPoint, hb]
  · have hdiag : (Matrix.diagonal
        (fun x : Qubits n => ((1 - 2 * boolPoint x j : ℝ) : ℂ))) x y = 0 := by
      exact Matrix.diagonal_apply_ne _ hxy
    rw [hdiag]
    change (if ∀ k : Fin n, k ∉ Set.range (wire1 j) → x k = y k then
      pauliZ (x j) (y j) else 0) = 0
    split_ifs with h
    · have hbit : x j ≠ y j := by
        intro heq
        apply hxy
        funext k
        by_cases hk : k = j
        · simpa [hk] using heq
        · apply h k
          rintro ⟨z, hz⟩
          exact hk hz.symm
      exact Matrix.diagonal_apply_ne _ hbit
    · rfl

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    let σ : Fin n → Matrix (Qubits n) (Qubits n) ℂ := fun j => CliffordOp.mat (CliffordOp.pauli j Pauli.Z)
    let H : Matrix (Qubits n) (Qubits n) ℂ :=
      ∑ j : Fin n, ∑ k : Fin n, ((A j k : ℝ) : ℂ) • (σ j * σ k) + ∑ j : Fin n, ((c j : ℝ) : ℂ) • σ j
    (∀ x : Qubits n,
      H x x = (((∑ j : Fin n, ∑ k : Fin n, A j k * (1 - 2 * boolPoint x j) * (1 - 2 * boolPoint x k)) +
        ∑ j : Fin n, c j * (1 - 2 * boolPoint x j) : ℝ) : ℂ)) ∧
      ∀ y w : Qubits n, y ≠ w → H y w = 0 := by
  classical
  dsimp only
  simp_rw [pauliZ_wire_diagonal, Matrix.diagonal_mul_diagonal]
  constructor
  · intro x
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.diagonal_apply_eq, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_sum, Complex.ofReal_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro y w hyw
    simp [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.diagonal_apply_ne _ hyw]
