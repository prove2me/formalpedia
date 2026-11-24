-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_apply_1ca466fba8a1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:59.576795+00:00
-- url     : https://prove2.me/submissions/351a6b3d-6dd2-4df9-b9c5-0816f636d618

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
variable {τ : Type} [DecidableEq τ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by
  by_cases h : c' = c <;> simp [lastToCoordinate, h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
