-- Prove2me | solution 1 for PI.SqPair.LCP.plane_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:00.231364+00:00
-- url     : https://prove2.me/submissions/124bc1d4-84ef-4af6-9ddd-c2fae5e0df1a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PlaneIsUnitOfSubOneMem
import Theorems.Thm_PI_SqPair_LCP_plane_isUnit_of_sub_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP
open Polynomial IsLocalRing Matrix
namespace PI.SqPair.LCP
theorem _root_.solution {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ t s c : R, β + t + σ t + t * σ t * α = 0 ∧
      s * (1 + t * α) + σ s * (1 + σ t * α) = -α ∧ c * (1 + t * α) = 1 ∧ ∃ s', s = α * s' := by
  have hfix : ∀ x : R₀, σ (x : R) = x := fun x => (hR₀ x).1 x.2
  have hNfix : σ (τ * σ τ) = τ * σ τ := by rw [map_mul, hσ, mul_comm]
  let N : R₀ := ⟨τ * σ τ, (hR₀ _).2 hNfix⟩
  have hN : (N : R) = τ * σ τ := rfl
  obtain ⟨w, hwroot, hw1⟩ := HenselianLocalRing.is_henselian (X ^ 2 - X + C (α * N * β))
    (by monicity!) 1
    (by
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, zero_add]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hα))
    (by
      simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
        eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]
      norm_num)
  have hr : w ^ 2 - w + α * N * β = 0 := by
    have h0 := hwroot.eq_zero
    simpa only [eval_add, eval_sub, eval_pow, eval_X, eval_C] using h0
  obtain ⟨wu, rfl⟩ := plane_isUnit_of_sub_one_mem hw1
  have hwv : (wu : R₀) * ↑wu⁻¹ = 1 := wu.mul_inv
  let x : R₀ := -β * ↑wu⁻¹
  have hx : β + x + α * N * x ^ 2 = 0 := by
    linear_combination (β * (↑wu⁻¹ : R₀) ^ 2) * hr -
      (β + β * ↑wu⁻¹ * ↑wu - β * ↑wu⁻¹) * hwv
  have hxR : (β : R) + x + α * (τ * σ τ) * (x : R) ^ 2 = 0 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) hx
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hN, ZeroMemClass.coe_zero]
      using h0
  let nR : R₀ := 1 + x * α + N * x ^ 2 * α ^ 2
  have hnm : nR - 1 ∈ maximalIdeal R₀ := by
    have e : nR - 1 = α * (x + N * x ^ 2 * α) := by ring
    rw [e]
    exact Ideal.mul_mem_right _ _ hα
  obtain ⟨nu, hnu⟩ := plane_isUnit_of_sub_one_mem hnm
  have hninv : ((nR : R₀) : R) * ((↑nu⁻¹ : R₀) : R) = 1 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) nu.mul_inv
    simpa only [hnu, Subring.coe_mul, OneMemClass.coe_one] using h0
  set t : R := τ * x with ht
  have hσt : σ t = σ τ * x := by rw [ht, map_mul, hfix]
  have hnR : (1 + t * α) * (1 + σ t * α) = ((nR : R₀) : R) := by
    rw [hσt, ht]
    simp only [nR]
    push_cast
    linear_combination ((x : R) * α) * hτ - ((x : R) ^ 2 * (α : R) ^ 2) * hN
  set c : R := (1 + σ t * α) * ((↑nu⁻¹ : R₀) : R) with hc
  have h3 : c * (1 + t * α) = 1 := by
    rw [hc]
    linear_combination ((↑nu⁻¹ : R₀) : R) * hnR + hninv
  have hσc : σ c = (1 + t * α) * ((↑nu⁻¹ : R₀) : R) := by
    rw [hc, map_mul, map_add, map_one, map_mul, hσ, hfix, hfix]
  refine ⟨t, -((α : R) * τ * c), c, ?_, ?_, h3, -(τ * c), by ring⟩
  · rw [hσt, ht]
    linear_combination hxR + (x : R) * hτ
  · rw [map_neg, map_mul, map_mul, hfix, hσc]
    linear_combination (-((α : R) * τ)) * h3 + (-((α : R) * σ τ * ((↑nu⁻¹ : R₀) : R))) * hnR +
      (-((α : R) * σ τ)) * hninv + (-(α : R)) * hτ
end PI.SqPair.LCP
