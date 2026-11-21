-- Prove2me | solution 1 for QuantumInfo.exists_kraus_mul_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:31.719174+00:00
-- url     : https://prove2.me/submissions/3b868c19-b4c4-48fb-9418-c5714dda7589

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_exists_smul_of_sum_conj_eq
public import Theorems.Thm_QuantumInfo_Channel_apply_def
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
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) {κ : Type*} [Fintype κ]
    (R : Channel n n κ) {F : Matrix n n ℂ} {lam : ℂ}
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = lam • ρ) (k : κ) :
    ∃ μ : ℂ, R.kraus k * F * P = μ • P := by
  refine exists_smul_of_sum_conj_eq hP (fun k => R.kraus k * F * P) lam
    (fun k => by rw [Matrix.mul_assoc, hP.mul_self]) (fun X => ?_) k
  have hX : P * X * P = P * (P * X * P) * P := by
    conv_rhs => rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self,
      Matrix.mul_assoc (P * X), hP.mul_self]
  have h1 := h (P * X * P) hX
  rw [Channel.apply_def] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
  simp only [Matrix.mul_assoc]
end QuantumInfo
