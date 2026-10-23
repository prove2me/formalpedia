-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.filtered_noisy_complement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:44:28.389732+00:00
-- url     : https://prove2.me/submissions/3f11091a-8098-4855-85f9-8b8ffccd2ae4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_scale (T : K → Matrix A A ℂ) (c : K → ℂ) (rho : Matrix A A ℂ) (k k' : K) :
    complementaryChannel (indexedKrausDilation (fun k => c k • T k)) rho k k' =
      c k * star (c k') * complementaryChannel (indexedKrausDilation T) rho k k' := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, mul_apply, conjTranspose_apply,
    indexedKrausDilation, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl
    fun a _ => ?_
  ring

theorem x8_main [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (a : K → ℝ) (ha : ProbabilityWeights a) :
    ∀ rho : Matrix A A ℂ,
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        (weightRoot a * noisyComplement T.matrix rho * weightRoot a) ∧
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        Matrix.hadamard (fun j k => (Real.sqrt (a j) : ℂ) * (Real.sqrt (a k) : ℂ))
          (noisyComplement T.matrix rho) := by
  intro rho
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have key : ∀ j k, randomComplement T.matrix a rho j k = (Fintype.card A : ℂ)^2 *
      ((Real.sqrt (a j) : ℂ) * (Real.sqrt (a k) : ℂ) * noisyComplement T.matrix rho j k) := by
    intro j k
    unfold randomComplement noisyComplement weightedKraus
    rw [x8_scale T.matrix (fun k => (Real.sqrt (a k) : ℂ)),
      x8_scale T.matrix (fun _ => (Fintype.card A : ℂ)⁻¹)]
    simp only [Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_natCast]
    field_simp
  have e1 : randomComplement T.matrix a rho = Matrix.of fun j k => (Fintype.card A : ℂ)^2 *
      ((Real.sqrt (a j) : ℂ) * (Real.sqrt (a k) : ℂ) * noisyComplement T.matrix rho j k) := by
    ext j k; rw [key]; rfl
  rw [e1]
  generalize noisyComplement T.matrix rho = N
  refine ⟨?_, ?_⟩
  · ext j k
    simp only [Matrix.smul_apply, weightRoot, diagonal_mul, mul_diagonal, smul_eq_mul, of_apply]
    ring
  · ext j k
    simp only [Matrix.smul_apply, smul_eq_mul, of_apply]
    rfl

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix in
open QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty K]
    (T : UnitaryBasis A K) (a : K → ℝ) (ha : ProbabilityWeights a) :
    ∀ rho : Matrix A A ℂ,
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        (weightRoot a * noisyComplement T.matrix rho * weightRoot a) ∧
      randomComplement T.matrix a rho = (Fintype.card A : ℂ)^2 •
        Matrix.hadamard (fun j k => (Real.sqrt (a j) : ℂ) * (Real.sqrt (a k) : ℂ))
          (noisyComplement T.matrix rho) :=
  x8_main T a ha
