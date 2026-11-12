-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P89.appendix_pauli_reordering
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:02:12.517273+00:00
-- url     : https://prove2.me/submissions/b3a52ee5-fa3a-422f-9fd0-ed2a3a11ebcb

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

noncomputable section

namespace Aux_pauli_reordering

open QAlgorithms.Papers.Independent.Intakenext100.P89

theorem zconj (a : PauliBasis) (f r : Bool) :
    (conditionalZ f).conjTranspose * pauliProjector a r * conditionalZ f =
      pauliProjector a (xor r (zOutcomeFlip a f)) := by
  cases a <;> cases f <;> cases r <;> ext i j <;> cases i <;> cases j <;>
    simp [conditionalZ, pauliProjector, basisObservable, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, zOutcomeFlip, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
      Matrix.diagonal_apply] <;> ring

theorem hconj (a : PauliBasis) (r : Bool) :
    QAlgorithms.hadamard.conjTranspose * pauliProjector a r * QAlgorithms.hadamard =
      pauliProjector (hadamardBasis a) (xor r (hadamardOutcomeFlip a)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  have hcc : c * c = 2⁻¹ := by
    rw [hc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hcs : star c = c := by
    rw [hc]
    simp
  obtain ⟨K, hK⟩ : ∃ K : Matrix Bool Bool ℂ,
      K = Matrix.of fun a b => if a && b then (-1 : ℂ) else 1 := ⟨_, rfl⟩
  have hH : QAlgorithms.hadamard = c • K := by
    ext i j
    cases i <;> cases j <;> simp [QAlgorithms.hadamard, hK, hc]
  rw [hH]
  simp only [Matrix.conjTranspose_smul, hcs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc]
  cases a <;> cases r <;> ext i j <;> cases i <;> cases j <;>
    simp [hK, pauliProjector, basisObservable, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, hadamardBasis, hadamardOutcomeFlip, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.one_apply, Matrix.diagonal_apply] <;> ring

end Aux_pauli_reordering

open QAlgorithms.Papers.Independent.Intakenext100.P89 Aux_pauli_reordering in
theorem solution {O R : Type*} [Fintype O] [Nonempty O]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (MA : O → Matrix Bool Bool ℂ)
    (hMA : ∑ o, (MA o).conjTranspose * MA o = 1)
    (feed : O → Bool) (U : O → Bool → Matrix.unitaryGroup R ℂ) :
    (∀ (rho : Matrix ((Bool × Bool) × R) ((Bool × Bool) × R) ℂ),
      QAlgorithms.IsDensityMatrix rho → ∀ (a : PauliBasis) (o : O) (r : Bool),
        latePauliBranch MA feed U a o r rho =
          earlyPauliBranch MA feed U a o (xor r (zOutcomeFlip a (feed o))) rho) ∧
    (∀ (rho : Matrix (Bool × R) (Bool × R) ℂ), QAlgorithms.IsDensityMatrix rho →
      ∀ (a : PauliBasis) (r : Bool),
        effectDiscard (QAlgorithms.hadamard.conjTranspose * pauliProjector a r *
          QAlgorithms.hadamard) rho =
        effectDiscard (pauliProjector (hadamardBasis a)
          (xor r (hadamardOutcomeFlip a))) rho) := by
  constructor
  · intro rho _ a o r
    unfold latePauliBranch earlyPauliBranch
    rw [zconj]
    generalize zOutcomeFlip a (feed o) = x
    cases r <;> cases x <;> rfl
  · intro rho _ a r
    rw [hconj]

end
