-- Prove2me | solution 1 for QuantumInfo.encoder_apply_of_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:25.842764+00:00
-- url     : https://prove2.me/submissions/761bd8dc-846d-47ba-8cc8-441c9a28a314

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_encoder_of_knillLaflamme

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
omit [Fintype ι] [DecidableEq ι] [Fintype L]
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) {i₀ : ι} (hi₀ : E i₀ = 1) (j : ι) :
    Vᴴ * E j * V = c i₀ j • 1 := by
  have h := encoder_of_knillLaflamme hP hV hPV hc i₀ j
  rwa [hi₀, conjTranspose_one, Matrix.mul_one] at h
end QuantumInfo
