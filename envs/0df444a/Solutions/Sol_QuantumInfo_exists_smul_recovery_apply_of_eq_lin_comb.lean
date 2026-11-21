-- Prove2me | solution 1 for QuantumInfo.exists_smul_recovery_apply_of_eq_lin_comb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:19.745166+00:00
-- url     : https://prove2.me/submissions/fe6d5376-1fa8-465c-ae3b-c0269a6fd5b1

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_recovery_apply_lin_comb

set_option autoImplicit false
@[expose] public section
public section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}
omit [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    {F : Matrix n n ℂ} {a : ι → ℂ} (hF : F = ∑ i, a i • E i) :
    ∃ γ : ℂ, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = γ • ρ := by
  refine ⟨∑ i, ∑ j, star (a i) * a j * c i j, fun ρ hρ => ?_⟩
  rw [hF]
  exact recovery_apply_lin_comb hR a hρ
end QuantumInfo
