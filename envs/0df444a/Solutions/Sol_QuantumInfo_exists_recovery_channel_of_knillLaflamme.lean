-- Prove2me | solution 1 for QuantumInfo.exists_recovery_channel_of_knillLaflamme
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:52:11.283119+00:00
-- url     : https://prove2.me/submissions/02f3cbbd-7cd3-47e3-b475-ca710a6ffec2

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Theorems.Thm_QuantumInfo_IsCodeProjector_smul_injective
public import Theorems.Thm_QuantumInfo_Channel_apply_sum
public import Theorems.Thm_QuantumInfo_exists_recovery_of_knillLaflamme
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
namespace QuantumInfo
theorem _root_.solution (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (𝓔 : Channel n n ι) (hc : KnillLaflamme P 𝓔.kraus c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      R.apply (𝓔.apply ρ) = ρ := by
  obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
  refine ⟨R, fun ρ hρ => ?_⟩
  rw [Channel.apply_def 𝓔 ρ, Channel.apply_sum]
  simp only [hR ρ hρ]
  rw [← Finset.sum_smul]
  have htr : ∑ i, c i i = 1 := by
    have h1 : P = (∑ i, c i i) • P := by
      calc P = P * (∑ i, (𝓔.kraus i)ᴴ * 𝓔.kraus i) * P := by
              rw [𝓔.tp, Matrix.mul_one, hP.mul_self]
        _ = ∑ i, P * (𝓔.kraus i)ᴴ * 𝓔.kraus i * P := by
              simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = ∑ i, c i i • P := Finset.sum_congr rfl fun i _ => hc i i
        _ = (∑ i, c i i) • P := Finset.sum_smul.symm
    exact (IsCodeProjector.smul_injective hP0 (by rw [one_smul, ← h1])).symm
  rw [htr, one_smul]
end QuantumInfo
