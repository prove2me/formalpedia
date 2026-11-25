-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:52.643794+00:00
-- url     : https://prove2.me/submissions/f93d6e18-4f85-4f9b-acc1-edfaa25fbb76

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
    (X : Ω) (k₀ k₁ k : κ) (hφ : ∀ k q, φ k (b q) = X * g k q)
    (hg : g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0) (a : Φ) :
    T.lineVal e (φ k) a =
      algebraMap Ω Φ ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₀) a +
        algebraMap Ω Φ ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) *
          T.lineVal e (φ k₁) a := by
  have hlin : φ k = ((g k 0 * g k₁ 1 - g k 1 * g k₁ 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₀ +
      ((g k₀ 0 * g k 1 - g k₀ 1 * g k 0) / (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0)) • φ k₁ := by
    refine b.ext fun q => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hφ, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hg]
    fin_cases q <;> simp <;> ring
  rw [hlin]
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring
end RatioField
end GroundTheory.Heights₂.Heights.Inter
