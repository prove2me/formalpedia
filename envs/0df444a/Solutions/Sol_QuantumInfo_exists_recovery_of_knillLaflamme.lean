-- Prove2me | solution 1 for QuantumInfo.exists_recovery_of_knillLaflamme
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:51:36.407928+00:00
-- url     : https://prove2.me/submissions/7a88e87e-d374-4d6c-ae06-0b9f5fc54144

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_IsCodeProjector_nonneg_of_smul_posSemidef
public import Theorems.Thm_QuantumInfo_KnillLaflamme_isHermitian
public import Theorems.Thm_QuantumInfo_Channel_apply_sum
public import Theorems.Thm_QuantumInfo_recoveryChannel_apply
public import Theorems.Thm_QuantumInfo_knillLaflamme_canonicalError
public import Theorems.Thm_QuantumInfo_eq_sum_canonicalError
public import Theorems.Thm_QuantumInfo_knillLaflamme_matrix_apply
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
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by
  have hc' := hc.isHermitian hP hP0
  set U : Matrix ι ι ℂ := klUnitary hc' with hU
  set F := canonicalError hc' E with hFdef
  set d := hc'.eigenvalues with hddef
  have hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0 :=
    fun k l => knillLaflamme_canonicalError hc' hc k l
  have hd : ∀ k, 0 ≤ d k := by
    intro k
    refine hP.nonneg_of_smul_posSemidef hP0 ?_
    have h := hF k k
    rw [if_pos rfl] at h
    rw [← h]
    have h2 : P * (F k)ᴴ * F k * P = (F k * P)ᴴ * (F k * P) := by
      rw [conjTranspose_mul, hP.conjTranspose_eq]
      simp only [Matrix.mul_assoc]
    rw [h2]
    exact posSemidef_conjTranspose_mul_self _
  refine ⟨recoveryChannel hP hd hF, fun ρ hρ i j => ?_⟩
  have hE : ∀ i, E i = ∑ k, star (U i k) • F k := fun i => eq_sum_canonicalError hc' i
  have hEH : ∀ j, (E j)ᴴ = ∑ l, U j l • (F l)ᴴ := by
    intro j
    rw [hE j, conjTranspose_sum]
    simp only [conjTranspose_smul, star_star]
  rw [hE i, hEH j]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Channel.apply_sum, Channel.apply_smul, recoveryChannel_apply hP hd hF hρ]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul]
  rw [← Finset.sum_smul, knillLaflamme_matrix_apply hc' i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end QuantumInfo
