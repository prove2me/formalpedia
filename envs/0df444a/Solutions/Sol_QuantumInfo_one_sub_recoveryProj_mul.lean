-- Prove2me | solution 1 for QuantumInfo.one_sub_recoveryProj_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:50:00.336335+00:00
-- url     : https://prove2.me/submissions/ce7e0f07-1c07-44cc-b967-10917f04630d

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_mul_codeProj_eq_zero_of_eq_zero
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
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (k : κ) :
    (1 - recoveryProj P F d) * F k * P = 0 := by
  have hF' : ∀ k l, P * ((F k)ᴴ * (F l * P)) = if k = l then ((d k : ℝ) : ℂ) • P else 0 :=
    fun k l => by simpa only [Matrix.mul_assoc] using hF k l
  have h : recoveryProj P F d * F k * P = F k * P := by
    rw [recoveryProj_eq hP hd, Finset.sum_mul, Finset.sum_mul, Finset.sum_eq_single k]
    · unfold errorImageProj
      split_ifs with hk
      · rw [mul_codeProj_eq_zero_of_eq_zero hP hF hk]
        simp
      · simp only [Matrix.smul_mul, Matrix.mul_assoc]
        rw [hF' k k, if_pos rfl, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
          inv_mul_cancel₀ hk, Complex.ofReal_one, one_smul]
    · intro m _ hmk
      unfold errorImageProj
      split_ifs with hm
      · simp
      · simp only [Matrix.smul_mul, Matrix.mul_assoc]
        rw [hF' m k, if_neg hmk]
        simp
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [sub_mul, sub_mul, one_mul, h, sub_self]
end QuantumInfo
