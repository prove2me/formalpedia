-- Prove2me | solution 1 for QuantumInfo.conjTranspose_mul_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:23.868127+00:00
-- url     : https://prove2.me/submissions/7d344901-1bc2-4c9f-bd74-3e643f195d99

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme

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
theorem _root_.solution (hV : Vᴴ * V = 1) : Vᴴ * (V * Vᴴ) = Vᴴ := by
  rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
end QuantumInfo
