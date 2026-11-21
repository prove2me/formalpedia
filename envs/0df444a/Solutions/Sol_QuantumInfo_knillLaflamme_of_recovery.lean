-- Prove2me | solution 1 for QuantumInfo.knillLaflamme_of_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:52:17.855422+00:00
-- url     : https://prove2.me/submissions/a400e024-b5a6-4ac6-8235-2cc7c6817e59

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_exists_kraus_mul_mul_eq_smul
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
    (R : Channel n n κ) (lam : ι → ℂ)
    (h : ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by
  have hscal : ∀ i k, ∃ μ : ℂ, R.kraus k * E i * P = μ • P := fun i k =>
    exists_kraus_mul_mul_eq_smul hP R (h i) k
  choose μ hμ using hscal
  refine ⟨fun i j => ∑ k, star (μ i k) * μ j k, fun i j => ?_⟩
  calc P * (E i)ᴴ * E j * P
      = P * (E i)ᴴ * (∑ k, (R.kraus k)ᴴ * R.kraus k) * E j * P := by
        rw [R.tp, Matrix.mul_one]
    _ = ∑ k, (R.kraus k * E i * P)ᴴ * (R.kraus k * E j * P) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, conjTranspose_mul, hP.conjTranspose_eq,
          Matrix.mul_assoc]
    _ = ∑ k, (star (μ i k) * μ j k) • P := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hμ i k, hμ j k, conjTranspose_smul, hP.conjTranspose_eq, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, hP.mul_self]
    _ = (∑ k, star (μ i k) * μ j k) • P := by rw [Finset.sum_smul]
end QuantumInfo
