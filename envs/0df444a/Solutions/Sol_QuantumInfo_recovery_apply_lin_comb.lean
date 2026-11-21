-- Prove2me | solution 1 for QuantumInfo.recovery_apply_lin_comb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:36.253187+00:00
-- url     : https://prove2.me/submissions/d4b7e38d-2bfd-414f-80e9-e7cf734b23c8

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_Channel_apply_sum
public import Theorems.Thm_QuantumInfo_Channel_apply_smul
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
omit [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    (a : ι → ℂ) {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) :
    R.apply ((∑ i, a i • E i) * ρ * (∑ i, a i • E i)ᴴ)
      = (∑ i, ∑ j, star (a i) * a j * c i j) • ρ := by
  rw [conjTranspose_sum]
  simp only [conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Channel.apply_sum, Channel.apply_smul, hR ρ hρ, smul_smul, ← Finset.sum_smul]
  refine congrArg (fun t : ℂ => t • ρ) (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end QuantumInfo
