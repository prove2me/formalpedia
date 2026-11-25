-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:40.491808+00:00
-- url     : https://prove2.me/submissions/0b732052-22bb-4a22-9d64-f387594ed57a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]
variable {E κ : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Inter
namespace RatioField
theorem _root_.solution (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (g : κ → Fin 2 → Ω)
    (X : Ω) (hX : X ≠ 0) (k₀ k₁ : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) :
    φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
  have hval : ∀ k q, φ k (b q) = e.repr (b q) 0 * φ k (e 0) + e.repr (b q) 1 * φ k (e 1) := by
    intro k q
    conv_lhs => rw [← e.sum_repr (b q)]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_eq_mul]
  intro h
  apply hg
  have hX2 : X * X ≠ 0 := mul_ne_zero hX hX
  apply (mul_right_injective₀ hX2).eq_iff.mp
  have h00 := hval k₀ 0
  have h01 := hval k₀ 1
  have h10 := hval k₁ 0
  have h11 := hval k₁ 1
  rw [hφ] at h00 h01 h10 h11
  linear_combination (X * g k₀ 0) * h11 + (e.repr (b 1) 1 * φ k₁ (e 1) + e.repr (b 1) 0 * φ k₁ (e 0)) * h00 -
    (X * g k₀ 1) * h10 - (e.repr (b 0) 1 * φ k₁ (e 1) + e.repr (b 0) 0 * φ k₁ (e 0)) * h01 +
    -(e.repr (b 0) 0 * e.repr (b 1) 1 - e.repr (b 0) 1 * e.repr (b 1) 0) * h
end RatioField
end GroundTheory.Heights₂.Heights.Inter
