-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_matrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:32.909751+00:00
-- url     : https://prove2.me/submissions/578cbce6-0a4f-4eff-9110-300f71cdbe35

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_eq_klUnitary_mul_diagonal
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
namespace QuantumInfo
theorem _root_.solution (i j : ι) :
    c j i = ∑ k, klUnitary hc' j k * (hc'.eigenvalues k : ℂ) * star (klUnitary hc' i k) := by
  conv_lhs => rw [eq_klUnitary_mul_diagonal hc']
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
  rfl
end QuantumInfo
