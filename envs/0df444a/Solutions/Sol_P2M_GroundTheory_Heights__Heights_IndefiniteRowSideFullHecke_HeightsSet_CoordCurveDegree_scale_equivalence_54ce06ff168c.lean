-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_scale_equivalence_54ce06ff168c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:57.306147+00:00
-- url     : https://prove2.me/submissions/7a46ad82-b77a-4bb5-bba8-450bbfda6569

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution (W : Ideal (MRing ι)) :
    Equivalence (fun z z' : mcPts W ↦ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) := by
  refine ⟨fun z ↦ ⟨1, fun _ ↦ one_ne_zero, by funext p; simp⟩, ?_, ?_⟩
  · rintro z z' ⟨c, hc, h⟩
    refine ⟨c⁻¹, fun k ↦ inv_ne_zero (hc k), funext fun p ↦ ?_⟩
    rw [h]
    simp [inv_mul_cancel_left₀ (hc p.1)]
  · rintro z z' z'' ⟨c, hc, h⟩ ⟨c', hc', h'⟩
    refine ⟨c' * c, fun k ↦ mul_ne_zero (hc' k) (hc k), funext fun p ↦ ?_⟩
    rw [h', h]
    simp [mul_assoc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
