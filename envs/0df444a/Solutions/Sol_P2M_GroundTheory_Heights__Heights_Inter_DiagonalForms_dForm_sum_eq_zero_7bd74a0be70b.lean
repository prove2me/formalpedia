-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_sum_eq_zero_7bd74a0be70b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:48.955504+00:00
-- url     : https://prove2.me/submissions/fa1dfd21-2d14-4dec-a1f1-d6a4de53423b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalForms
theorem _root_.solution {κ : Type*} [Fintype κ] (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hd : ∀ k k', φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1) = 0) (c c' : κ → Ω) (s : Ω) :
    (∑ k, c k • s • φ k) (e 0) * (∑ k, c' k • s • φ k) (e 1) -
      (∑ k, c' k • s • φ k) (e 0) * (∑ k, c k • s • φ k) (e 1) = 0 := by
  rw [mul_comm ((∑ k, c' k • s • φ k) (e 0))]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k' _ => ?_
  linear_combination (c k * c' k' * s ^ 2) * hd k k'
end GroundTheory.Heights₂.Heights.Inter.DiagonalForms
