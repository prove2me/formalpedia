-- Prove2me | solution 1 for QuantumInfo.KnillLaflamme.isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:25.478907+00:00
-- url     : https://prove2.me/submissions/e5b2694a-f514-4d66-b739-6b03e480a693

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_IsCodeProjector_smul_injective
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
omit [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace QuantumInfo
namespace KnillLaflamme
theorem _root_.solution (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) : c.IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  have h3 : (P * (E j)ᴴ * E i * P)ᴴ = P * (E i)ᴴ * E j * P := by
    simp [conjTranspose_mul, hP.conjTranspose_eq, Matrix.mul_assoc]
  rw [hc j i, conjTranspose_smul, hP.conjTranspose_eq, hc i j] at h3
  exact IsCodeProjector.smul_injective hP0 h3
end KnillLaflamme
end QuantumInfo
