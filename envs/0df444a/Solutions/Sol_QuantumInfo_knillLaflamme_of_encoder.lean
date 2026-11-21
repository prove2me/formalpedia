-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_of_encoder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:33.452767+00:00
-- url     : https://prove2.me/submissions/cd218691-eaa7-4cd2-b3f0-640a5fc1d285

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
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
variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}
omit [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution
    (h : ∀ i j, Vᴴ * (E i)ᴴ * E j * V = c i j • 1) :
    KnillLaflamme (V * Vᴴ) E c := by
  intro i j
  calc V * Vᴴ * (E i)ᴴ * E j * (V * Vᴴ)
      = V * (Vᴴ * (E i)ᴴ * E j * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * (c i j • (1 : Matrix L L ℂ)) * Vᴴ := by rw [h i j]
    _ = c i j • (V * Vᴴ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
end QuantumInfo
