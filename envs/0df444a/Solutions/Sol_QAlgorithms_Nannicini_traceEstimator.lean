-- Prove2me | solution 1 for QAlgorithms.Nannicini.traceEstimator
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:03:57.926907+00:00
-- url     : https://prove2.me/submissions/a3c7d677-1fa0-4593-bc00-d06c5cf8a4d6

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open QAlgorithms
open scoped Matrix.Norms.L2Operator ComplexOrder

private lemma te_reindex_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.submatrix e e ∈ Matrix.unitaryGroup κ ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change U.submatrix e e * (U.submatrix e e).conjTranspose = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact (congrArg (fun M : Matrix ι ι ℂ => M.submatrix e e) hU.2).trans
    (Matrix.submatrix_one_equiv e)

private def te_oracle : Matrix (Qubits (1 + 0)) (Qubits (1 + 0)) ℂ :=
  pauliX.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool)

private lemma te_block_zero :
    (Matrix.of fun i j : Qubits 0 =>
      te_oracle ((qubitsAppendEquiv 1 0).symm (0,i))
        ((qubitsAppendEquiv 1 0).symm (0,j))) = 0 := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [te_oracle, qubitsAppendEquiv, Equiv.funUnique, pauliX]

private lemma te_encoding (r : ℝ) (hr : |r| ≤ 1 / 2) :
    IsBlockEncoding (0 : Qubits 1)
      (te_oracle.submatrix (qubitsAppendEquiv 1 0).symm (qubitsAppendEquiv 1 0).symm)
      1 (1 / 2) ((r : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ)) := by
  have hX : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change pauliX * pauliX.conjTranspose = 1
    ext i j
    cases i <;> cases j <;>
      norm_num [pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ⟨te_reindex_unitary _ _ (te_reindex_unitary _ _ hX), ?_⟩
  change specNorm ((1 : ℂ) • (Matrix.of fun i j : Qubits 0 =>
      te_oracle ((qubitsAppendEquiv 1 0).symm (0,i))
        ((qubitsAppendEquiv 1 0).symm (0,j))) - _) ≤ _
  rw [te_block_zero, smul_zero, zero_sub]
  simpa [specNorm, norm_smul, Complex.norm_real, Real.norm_eq_abs] using hr

private lemma te_hermitian (r : ℝ) :
    ((r : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  simp

private lemma te_real (r : ℝ) (i j : Qubits 0) :
    (((r : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ)) i j).im = 0 := by
  simp [Subsingleton.elim i j]

private lemma te_norm (r : ℝ) :
    specNorm ((r : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ)) = |r| := by
  simp [specNorm, norm_smul, Real.norm_eq_abs]

private lemma te_density : IsDensityMatrix (1 : Matrix (Qubits 0) (Qubits 0) ℂ) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  simp [Matrix.trace_one, Qubits]

private lemma te_trace (r : ℝ) :
    (((r : ℂ) • (1 : Matrix (Qubits 0) (Qubits 0) ℂ)) * 1).trace.re = r := by
  simp [Matrix.trace_smul, Matrix.trace_one, Qubits]

theorem solution : ¬ (
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∀ (q a : ℕ) (α θ : ℝ), 0 < α → 0 < θ →
      ∃ (w : ℕ) (V : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => a + q) (q + w))
        (Y : Qubits (q + w) → ℝ),
        (V.queryCount 0 : ℝ) ≤ C * (α + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
          Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        (V.gateCount : ℝ) ≤
          C * (α + 1) * ((a : ℝ) + 1) * (Real.log (2 + α) + Real.log (2 + 1 / θ) +
            Real.log (2 + (q : ℝ)) + Real.log (2 + (a : ℝ))) ^ c ∧
        ∀ (A : Matrix (Qubits q) (Qubits q) ℂ) (U : Matrix (Qubits (a + q)) (Qubits (a + q)) ℂ)
          (ρ : Matrix (Qubits q) (Qubits q) ℂ),
          A.IsHermitian → (∀ i j, (A i j).im = 0) → specNorm A ≤ 1 →
          IsBlockEncoding (0 : Qubits a)
            (U.submatrix (qubitsAppendEquiv a q).symm (qubitsAppendEquiv a q).symm) α (θ / 2) A →
          IsDensityMatrix ρ →
          |densityMean ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y - (A * ρ).trace.re| ≤ θ / 4 ∧
          densityVariance ((V.unitary fun _ => U) * withZeroAncillas ρ w *
              star (V.unitary fun _ => U)) Y ≤ C) := by
  classical
  rintro ⟨C, hC, c, h⟩
  obtain ⟨w, V, Y, hquery, hgate, hspec⟩ := h 0 1 1 1 (by norm_num) (by norm_num)
  have hp := (hspec (((1 / 2 : ℝ) : ℂ) • 1) te_oracle 1
    (te_hermitian _) (te_real _) (by rw [te_norm]; norm_num)
    (by simpa using te_encoding (1 / 2) (by norm_num)) te_density).1
  have hn := (hspec (((-1 / 2 : ℝ) : ℂ) • 1) te_oracle 1
    (te_hermitian _) (te_real _) (by rw [te_norm]; norm_num)
    (by simpa using te_encoding (-1 / 2) (by norm_num)) te_density).1
  rw [te_trace] at hp hn
  have hp' := (abs_le.mp hp).1
  have hn' := (abs_le.mp hn).2
  norm_num at hp' hn'
  linarith
