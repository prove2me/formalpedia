-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P03.code_covariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:12:11.086573+00:00
-- url     : https://prove2.me/submissions/5bfd9dc0-bacf-4e0a-838c-6495cc231a24

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

lemma e79_hw_sum {ι : Type*} [Fintype ι] (x : ι → Bool) :
    hammingWeight x = ∑ i, (if x i = true then 1 else 0) := by
  unfold hammingWeight
  rw [Finset.card_filter]

lemma e79_hw_split (n k : ℕ) (h : k ≤ n) (z : Qubits n) :
    hammingWeight z = hammingWeight (splitBits n k h z).1 + hammingWeight (splitBits n k h z).2 := by
  simp only [e79_hw_sum, splitBits, qubitsAppendEquiv, Equiv.coe_fn_mk]
  rw [← Fin.sum_univ_add (f := fun i => if z (Fin.cast (Nat.add_sub_of_le h) i) = true then 1 else 0)]
  exact (Fintype.sum_equiv (finCongr (Nat.add_sub_of_le h)) _ _ (fun i => rfl)).symm

end QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P03 in
theorem solution {n k alpha : ℕ} (A : Ancilla n k alpha)
    (U : (Matrix.unitaryGroup (Qubits n) ℂ)) (hU : Conserves U) : U1ChargeCovariant (chargeEncoder A U) := by
  intro theta rho _
  set f : ∀ m : ℕ, Qubits m → ℂ := fun m x => Complex.exp (Complex.I * (theta : ℂ) * (hammingWeight x : ℂ)) with hf
  have hR : ∀ m, chargeRotation m theta = Matrix.diagonal (f m) := fun m => rfl
  -- entrywise conservation
  have hUe : ∀ x y, (U : Matrix (Qubits n) (Qubits n) ℂ) x y ≠ 0 → hammingWeight x = hammingWeight y := by
    intro x y hxy
    have := congrFun (congrFun hU x) y
    simp only [hammingCharge, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h2 : (U : Matrix (Qubits n) (Qubits n) ℂ) x y * ((hammingWeight y : ℂ) - hammingWeight x) = 0 := by
      rw [mul_sub]; rw [this]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hxy
    · exact_mod_cast (sub_eq_zero.mp h).symm
  have hcomm : Matrix.diagonal (f n) * (U : Matrix (Qubits n) (Qubits n) ℂ) =
      (U : Matrix (Qubits n) (Qubits n) ℂ) * Matrix.diagonal (f n) := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : (U : Matrix (Qubits n) (Qubits n) ℂ) x y = 0
    · simp [h]
    · simp [hf, hUe x y h, mul_comm]
  have hcomm' : (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * (Matrix.diagonal (f n))ᴴ =
      (Matrix.diagonal (f n))ᴴ * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hcomm]
  -- eigen condition
  have hpsi : ∀ v : Qubits (n - k), A.vector v ≠ 0 → hammingWeight v = alpha := by
    intro v hv
    have := congrArg (fun φ : EuclideanSpace ℂ (Qubits (n-k)) => φ v) A.eigen
    simp only [act, hammingCharge, Matrix.mulVec_diagonal, PiLp.smul_apply, smul_eq_mul] at this
    have h2 : A.vector v * ((hammingWeight v : ℂ) - alpha) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hv
    · exact Nat.cast_injective (R := ℂ) (sub_eq_zero.mp h)
  have hmid : (Matrix.of fun z w => (Matrix.diagonal (f k) * rho * (Matrix.diagonal (f k))ᴴ)
        (splitBits n k A.logical_le z).1 (splitBits n k A.logical_le w).1 *
        A.vector (splitBits n k A.logical_le z).2 * conj (A.vector (splitBits n k A.logical_le w).2)) =
      Matrix.diagonal (f n) * (Matrix.of fun z w => rho (splitBits n k A.logical_le z).1 (splitBits n k A.logical_le w).1 *
        A.vector (splitBits n k A.logical_le z).2 * conj (A.vector (splitBits n k A.logical_le w).2)) *
        (Matrix.diagonal (f n))ᴴ := by
    ext z w
    simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply,
      Pi.star_apply]
    by_cases hz : A.vector (splitBits n k A.logical_le z).2 = 0
    · simp [hz]
    by_cases hw : A.vector (splitBits n k A.logical_le w).2 = 0
    · simp [hw]
    have ez := hpsi _ hz
    have ew := hpsi _ hw
    simp only [hf]
    rw [e79_hw_split n k A.logical_le z, e79_hw_split n k A.logical_le w]
    simp only [ez, ew]
    have hexp : ∀ a b : ℕ, Complex.exp (Complex.I * theta * ((a + b : ℕ) : ℂ)) =
        Complex.exp (Complex.I * theta * (a : ℂ)) * Complex.exp (Complex.I * theta * (b : ℂ)) := by
      intro a b; rw [← Complex.exp_add]; push_cast; ring_nf
    rw [hexp, hexp]
    have hunit : Complex.exp (Complex.I * theta * (alpha : ℂ)) * star (Complex.exp (Complex.I * theta * (alpha : ℂ))) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      simp [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    simp only [star_mul']
    linear_combination (rho (splitBits n k A.logical_le z).1 (splitBits n k A.logical_le w).1 *
      A.vector (splitBits n k A.logical_le z).2 * conj (A.vector (splitBits n k A.logical_le w).2) *
      Complex.exp (Complex.I * theta * (hammingWeight (splitBits n k A.logical_le z).1 : ℂ)) *
      star (Complex.exp (Complex.I * theta * (hammingWeight (splitBits n k A.logical_le w).1 : ℂ)))) * (1 - hunit)
  simp only [chargeEncoder, pureEncoder, hR]
  rw [hmid]
  have key : ∀ M : Matrix (Qubits n) (Qubits n) ℂ,
      (U : Matrix (Qubits n) (Qubits n) ℂ) * (Matrix.diagonal (f n) * M * (Matrix.diagonal (f n))ᴴ) *
        (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ =
      Matrix.diagonal (f n) * ((U : Matrix (Qubits n) (Qubits n) ℂ) * M * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ) *
        (Matrix.diagonal (f n))ᴴ := by
    intro M
    calc _ = ((U : Matrix (Qubits n) (Qubits n) ℂ) * Matrix.diagonal (f n)) * M *
          ((Matrix.diagonal (f n))ᴴ * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = (Matrix.diagonal (f n) * (U : Matrix (Qubits n) (Qubits n) ℂ)) * M *
          ((U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ * (Matrix.diagonal (f n))ᴴ) := by rw [← hcomm, ← hcomm']
      _ = _ := by simp only [Matrix.mul_assoc]
  exact key _
