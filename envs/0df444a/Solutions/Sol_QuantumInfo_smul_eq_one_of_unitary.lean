-- Prove2me | solution 1 for QuantumInfo.smul_eq_one_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:26.571777+00:00
-- url     : https://prove2.me/submissions/acb65c52-2167-47a5-810a-b3cddf4b9c27

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_Channel_apply_trace


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
namespace QuantumInfo
theorem _root_.solution {κ : Type*} [Fintype κ] (R : Channel n n κ)
    {E ρ : Matrix n n ℂ} (hE : Eᴴ * E = 1) {γ : ℂ}
    (h : R.apply (E * ρ * Eᴴ) = γ • ρ) (hρ : ρ.trace ≠ 0) : γ = 1 := by
  have h1 : (E * ρ * Eᴴ).trace = ρ.trace := by
    rw [Matrix.trace_mul_cycle, hE, Matrix.one_mul]
  refine mul_right_cancel₀ hρ ?_
  calc γ * ρ.trace = (γ • ρ).trace := by rw [Matrix.trace_smul, smul_eq_mul]
    _ = (R.apply (E * ρ * Eᴴ)).trace := by rw [h]
    _ = (E * ρ * Eᴴ).trace := R.apply_trace _
    _ = ρ.trace := h1
    _ = 1 * ρ.trace := (one_mul _).symm
end QuantumInfo
