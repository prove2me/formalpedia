-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceRegTail_exists_bound_d01650779eca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:34.088099+00:00
-- url     : https://prove2.me/submissions/1a553dd0-5380-4983-aceb-0357229bad81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegVarBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutTailMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceRegTail

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
open MvPolynomial Filter Topology Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace SliceRegTail
theorem _root_.solution {n : ℕ} {a : (Fin n → ℂ) → ℝ}
    (ha : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → a (t • x) = a x) (hac : ContinuousOn a {x | x ≠ 0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |a x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (hac.mono fun x hx => ne_zero_of_mem_unit_sphere ⟨x, hx⟩)
  refine ⟨max C₀ |a 0| + 1, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; linarith [le_max_right C₀ |a 0|]
  · have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    have hy : (‖x‖ : ℂ)⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have := hC₀ _ hy
    rw [Real.norm_eq_abs, ← ha (‖x‖ : ℂ) _ hn, smul_inv_smul₀ hn] at this
    linarith [le_max_left C₀ |a 0|]
end SliceRegTail
end GroundTheory.Heights₂.Heights
