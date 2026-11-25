-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_blockFnField_eq_2808a9951dc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:20.259591+00:00
-- url     : https://prove2.me/submissions/2e2ddb83-ccdf-4e0f-b407-dab7d11bcdc4

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
theorem _root_.solution (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    blockFnField y =
      IntermediateField.adjoin ℚ (Set.range fun p : Σ k, ι k ↦ y p / y ⟨p.1, d p.1⟩) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro t ⟨p, q, hpq, rfl⟩
    have e : y p / y q = (y p / y ⟨p.1, d p.1⟩) / (y q / y ⟨q.1, d q.1⟩) := by
      rw [hpq, div_div_div_cancel_right₀ (hd q.1)]
    rw [e]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
  · rintro t ⟨p, rfl⟩
    exact ratio_mem y rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
