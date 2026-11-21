-- Prove2me | solution 1 for QuantumInfo.mul_conjTranspose_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:08.556665+00:00
-- url     : https://prove2.me/submissions/0a2153b5-a105-4049-93df-0f02697740ae

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
omit [DecidableEq n]
namespace QuantumInfo
theorem _root_.solution [Nonempty L] (hV : Vᴴ * V = 1) : V * Vᴴ ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty L›
  have h1 : (1 : Matrix L L ℂ) = 0 := by
    calc (1 : Matrix L L ℂ) = Vᴴ * V * (Vᴴ * V) := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (V * Vᴴ) * V := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have h2 : (1 : ℂ) = 0 := by
    have h3 := congrFun (congrFun h1 i) i
    rwa [Matrix.one_apply_eq, Matrix.zero_apply] at h3
  exact one_ne_zero h2
end QuantumInfo
