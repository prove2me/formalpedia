-- Prove2me | solution 1 for QuantumInfo.exists_knillLaflamme_of_encoderKL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:19.204168+00:00
-- url     : https://prove2.me/submissions/ee1216d9-fb43-407d-8691-cd40c16f69aa

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_knillLaflamme_of_encoder
public import Theorems.Thm_QuantumInfo_encoderKL_iff

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
theorem _root_.solution (h : EncoderKL V E) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme (V * Vᴴ) E c :=
  ⟨Matrix.of fun i j => ((encoderKL_iff.mp h) i j).choose,
    knillLaflamme_of_encoder fun i j => ((encoderKL_iff.mp h) i j).choose_spec⟩
end QuantumInfo
