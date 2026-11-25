-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:47.410523+00:00
-- url     : https://prove2.me/submissions/4bec5c62-196e-45c0-9b50-9ce3935d9dd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ (δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  have hpow : ∀ δ₁ δ₂ : ι → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [Geo.chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨coordDeg n p, X p, isWeightedHomogeneous_X ℤ _ p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ coordDeg n p k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [coordDeg, hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [coordDeg]
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMonomial c δ₂ + e₂ * chartMonomial c δ₁,
      (h₁.mul (isWeightedHomogeneous_chartMonomial c δ₂)).add ?_, ?_⟩
    · rw [add_comm δ₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMonomial, aeval_chartMonomial, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, h₁.mul h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring
end GroundTheory.Heights₂.Heights.ChartLatSection
