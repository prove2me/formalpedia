-- Prove2me | solution 1 for QuantumInfo.recoveryOp_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:04.577843+00:00
-- url     : https://prove2.me/submissions/2ac4f456-0675-476f-a9c9-aafca77f191f

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_recoveryOp_mul_mul_codeProj
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
theorem _root_.solution (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (m k l : κ) :
    recoveryOp P F d m * (F k * ρ * (F l)ᴴ) * (recoveryOp P F d m)ᴴ
      = if m = k ∧ m = l ∧ d m ≠ 0 then ((d m : ℝ) : ℂ) • ρ else 0 := by
  have h1 : recoveryOp P F d m * (F k * ρ * (F l)ᴴ) * (recoveryOp P F d m)ᴴ
      = (recoveryOp P F d m * F k * P) * ρ * (recoveryOp P F d m * F l * P)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
    conv_lhs => rw [hρ]
    simp only [Matrix.mul_assoc]
  rw [h1, recoveryOp_mul_mul_codeProj hF m k, recoveryOp_mul_mul_codeProj hF m l]
  by_cases hmk : m = k
  · by_cases hml : m = l
    · by_cases hm : d m = 0
      · simp [hm]
      · rw [if_pos ⟨hmk, hm⟩, if_pos ⟨hml, hm⟩, if_pos ⟨hmk, hml, hm⟩, conjTranspose_smul,
          Complex.star_def, Complex.conj_ofReal, hP.conjTranspose_eq]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd m), ← hρ]
    · simp [hml]
  · simp [hmk]
end QuantumInfo
