-- Prove2me | solution 1 for QuantumInfo.eq_sum_canonicalError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:05.93451+00:00
-- url     : https://prove2.me/submissions/9ff2e62a-0ede-4310-910f-10d1007909b4

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_klUnitary_mul_star
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
omit [Fintype n] [DecidableEq n]
namespace QuantumInfo
theorem _root_.solution (i : ι) :
    E i = ∑ k, star (klUnitary hc' i k) • canonicalError hc' E k := by
  unfold canonicalError
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ k, (star (klUnitary hc' i k) * klUnitary hc' j k) • E j
      = ((klUnitary hc' * star (klUnitary hc')) j i) • E j := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.star_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [h, klUnitary_mul_star, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
end QuantumInfo
