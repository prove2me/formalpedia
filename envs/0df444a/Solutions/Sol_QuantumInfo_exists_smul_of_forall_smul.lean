-- Prove2me | solution 1 for QuantumInfo.exists_smul_of_forall_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:49:57.358946+00:00
-- url     : https://prove2.me/submissions/7b155604-2007-4df2-91da-e2c14abc3abb

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
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
theorem _root_.solution {A : Matrix n n ℂ}
    (hAP : A * P = A) (h : ∀ w : n → ℂ, ∃ α : ℂ, A *ᵥ w = α • (P *ᵥ w)) :
    ∃ μ : ℂ, A = μ • P := by
  by_cases hP0 : P = 0
  · exact ⟨0, by rw [← hAP, hP0, Matrix.mul_zero, zero_smul]⟩
  have hw₀ : ∃ w₀ : n → ℂ, P *ᵥ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP0
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [mulVec_single_one] using this
  obtain ⟨w₀, hw₀⟩ := hw₀
  obtain ⟨μ, hμ⟩ := h w₀
  have hAw : ∀ w, A *ᵥ w = A *ᵥ (P *ᵥ w) := fun w => by rw [mulVec_mulVec, hAP]
  have key : ∀ w, A *ᵥ w = μ • (P *ᵥ w) := by
    intro w
    obtain ⟨α, hα⟩ := h w
    by_cases hdep : ∃ t : ℂ, P *ᵥ w = t • (P *ᵥ w₀)
    · obtain ⟨t, ht⟩ := hdep
      rw [hAw, ht, mulVec_smul, ← hAw, hμ, smul_comm]
    · push Not at hdep
      obtain ⟨β, hβ⟩ := h (w + w₀)
      rw [mulVec_add, mulVec_add, hα, hμ, smul_add] at hβ
      have hli : LinearIndependent ℂ ![P *ᵥ w, P *ᵥ w₀] := by
        rw [linearIndependent_fin2]
        exact ⟨hw₀, fun t ht => hdep t ht.symm⟩
      have := hli.eq_of_pair (s := α) (t := μ) (s' := β) (t' := β) hβ
      rw [hα, this.1, this.2]
  refine ⟨μ, Matrix.ext fun i j => ?_⟩
  have := congrFun (key (Pi.single j 1)) i
  simpa [mulVec_single_one] using this
end QuantumInfo
