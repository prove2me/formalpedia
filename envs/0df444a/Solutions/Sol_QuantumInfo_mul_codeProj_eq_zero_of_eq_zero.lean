-- Prove2me | solution 1 for QuantumInfo.mul_codeProj_eq_zero_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:26.060963+00:00
-- url     : https://prove2.me/submissions/631701e1-68c3-4747-84f8-8a23971fdede

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
omit [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]
variable (P : Matrix n n ℂ) (F : κ → Matrix n n ℂ) (d : κ → ℝ)
variable [Fintype κ]
variable {P F d}
omit [DecidableEq n] [Fintype κ]
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {k : κ} (hk : d k = 0) : F k * P = 0 := by
  have h := hF k k
  rw [if_pos rfl, hk, Complex.ofReal_zero, zero_smul] at h
  have h2 : (F k * P)ᴴ * (F k * P) = 0 := by
    rw [conjTranspose_mul, hP.conjTranspose_eq, ← h]
    simp only [Matrix.mul_assoc]
  exact conjTranspose_mul_self_eq_zero.mp h2
end QuantumInfo
