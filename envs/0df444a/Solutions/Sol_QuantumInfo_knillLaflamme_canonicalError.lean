-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_canonicalError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:53.597412+00:00
-- url     : https://prove2.me/submissions/37e0fe15-9932-4ad5-bfc1-7c7eb545e0c6

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_star_klUnitary_mul_mul
public import Theorems.Thm_QuantumInfo_Channel_id_apply
attribute [local simp] QuantumInfo.Channel.id_apply



set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
variable (hc' : c.IsHermitian)
omit [DecidableEq n]
namespace QuantumInfo
theorem _root_.solution (hc : KnillLaflamme P E c) (k l : ι) :
    P * (canonicalError hc' E k)ᴴ * canonicalError hc' E l * P
      = if k = l then ((hc'.eigenvalues k : ℝ) : ℂ) • P else 0 := by
  have h1 : P * (canonicalError hc' E k)ᴴ * canonicalError hc' E l * P
      = ∑ j, ∑ i, (klUnitary hc' j l * star (klUnitary hc' i k) * c i j) • P := by
    unfold canonicalError
    rw [conjTranspose_sum]
    simp only [conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hc i j, smul_smul]
  rw [h1]
  have h2 : ∑ j, ∑ i, (klUnitary hc' j l * star (klUnitary hc' i k) * c i j) • P
      = (star (klUnitary hc') * c * klUnitary hc') k l • P := by
    simp only [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h2, star_klUnitary_mul_mul, diagonal_apply]
  split_ifs <;> simp
end QuantumInfo
