-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroCoordinate_apply_d48952ae67a2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:30.225488+00:00
-- url     : https://prove2.me/submissions/43de966c-1f6d-4054-839b-53d32ed38ee2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloEliminate

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {τ : Type} [DecidableEq τ] (c : τ) (y : τ → ℂ) (c' : τ) :
    zeroCoordinate c y c' = if c' = c then 0 else y c' := by
  by_cases h : c' = c <;> simp [zeroCoordinate, h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
