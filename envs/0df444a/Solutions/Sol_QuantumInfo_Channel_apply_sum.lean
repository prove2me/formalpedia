-- Prove2me | solution 1 for QuantumInfo.Channel.apply_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:48:18.49147+00:00
-- url     : https://prove2.me/submissions/18150b80-6fef-4d43-9bde-7fdb171d84ea

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_Channel_apply_def
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
omit [Fintype ι] [DecidableEq ι]
namespace QuantumInfo
namespace Channel
theorem _root_.solution {m κ : Type*} [Fintype m] [Fintype κ] (Φ : Channel n m κ)
    {α : Type*} (s : Finset α) (f : α → Matrix n n ℂ) :
    Φ.apply (∑ a ∈ s, f a) = ∑ a ∈ s, Φ.apply (f a) := by
  simp only [Channel.apply_def, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm
end Channel
end QuantumInfo
