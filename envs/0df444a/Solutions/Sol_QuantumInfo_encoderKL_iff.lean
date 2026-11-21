-- Prove2me | solution 1 for QuantumInfo.encoderKL_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:42.866521+00:00
-- url     : https://prove2.me/submissions/05823586-9871-4ecf-b174-e6416dd8dd02

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
omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L]
namespace QuantumInfo
theorem _root_.solution {E : ι → Matrix n n ℂ} :
    EncoderKL V E ↔ ∀ i j, ∃ γ : ℂ, Vᴴ * (E i)ᴴ * E j * V = γ • 1 := Iff.rfl
end QuantumInfo
