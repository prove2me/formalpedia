-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceBranchExists_proof_2b0caf1b15cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:41.624854+00:00
-- url     : https://prove2.me/submissions/748d3bbd-1917-4991-b271-0bad2a077be2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceOnComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPlaceBranchExists

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
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace PlaceBranchExists
theorem _root_.solution (h₁ : PlaceOnComponent.Statement) (h₂ : PrimePlaceBranchExists.Statement) :
    PlaceBranchExists.Statement := by
  intro n I q hrad hdim P
  obtain ⟨J, hJ, -, hdimJ, P', hP'⟩ := h₁ n I q hrad hdim P
  obtain ⟨ν, hν⟩ := h₂ n J q hJ.1.1 hdimJ P'

  let ν' : VarBranch I 1 q :=
    { radius := ν.radius, radius_pos := ν.radius_pos, toFun := ν.toFun, differentiableOn := ν.differentiableOn,
      injOn := ν.injOn, map_zero := ν.map_zero,
      mapsTo := fun t ht g hg ↦ ν.mapsTo ht g (hJ.1.2 hg) }
  have hord : ∀ f, branchOrder ν' f = branchOrder ν f := fun _ ↦ rfl
  exact ⟨ν', fun f ↦ (hP' f).trans ((hν f).trans (hord f).symm)⟩
end PlaceBranchExists
end GroundTheory.Heights₂.Heights
