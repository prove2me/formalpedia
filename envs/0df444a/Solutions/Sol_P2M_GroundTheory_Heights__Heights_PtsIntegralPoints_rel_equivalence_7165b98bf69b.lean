-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_rel_equivalence_7165b98bf69b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:30.12964+00:00
-- url     : https://prove2.me/submissions/76a62b66-bd6f-48cf-af6d-b8ca0893bdff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints

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
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsIntegralPoints
theorem _root_.solution (P : Ideal (Geo.MRing ι)) :
    Equivalence (fun z z' : Geo.mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) where
  refl z := ⟨fun _ ↦ 1, fun _ ↦ one_ne_zero, by funext p; simp⟩
  symm := by
    rintro z z' ⟨c, hc, h⟩
    refine ⟨fun k ↦ (c k)⁻¹, fun k ↦ inv_ne_zero (hc k), ?_⟩
    funext p
    rw [h]
    exact (inv_mul_cancel_left₀ (hc p.1) _).symm
  trans := by
    rintro z z' z'' ⟨c, hc, h⟩ ⟨d, hd, h'⟩
    refine ⟨fun k ↦ d k * c k, fun k ↦ mul_ne_zero (hd k) (hc k), ?_⟩
    funext p
    rw [h', h, mul_assoc]
end GroundTheory.Heights₂.Heights.PtsIntegralPoints
