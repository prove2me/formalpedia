-- Prove2me | solution 1 for QuantumInfo.exists_recovery_of_encoderKL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:52:11.821012+00:00
-- url     : https://prove2.me/submissions/bc23f8c4-b16f-4adc-879a-b180b84e627f

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_exists_recovery_of_knillLaflamme
public import Theorems.Thm_QuantumInfo_isCodeProjector_mul_conjTranspose
public import Theorems.Thm_QuantumInfo_mul_conjTranspose_ne_zero
public import Theorems.Thm_QuantumInfo_exists_knillLaflamme_of_encoderKL

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
theorem _root_.solution [Nonempty L] (hV : Vᴴ * V = 1) (h : EncoderKL V E) :
    ∃ (c : Matrix ι ι ℂ) (R : Channel n n (Option ι)),
      ∀ ρ : Matrix n n ℂ, ρ = V * Vᴴ * ρ * (V * Vᴴ) →
        ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by
  obtain ⟨c, hc⟩ := exists_knillLaflamme_of_encoderKL h
  obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme (isCodeProjector_mul_conjTranspose hV)
    (mul_conjTranspose_ne_zero hV) hc
  exact ⟨c, R, hR⟩
end QuantumInfo
