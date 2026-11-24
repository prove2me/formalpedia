-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:03.571004+00:00
-- url     : https://prove2.me/submissions/58b10ab1-f7bc-4a72-aa0b-a29a676d02a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.evalAt_apply
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_C

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
variable {d : ℕ} {y₀ : Fin d → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (y : Fin d → ℂ) (t : ℂ) : pev (y₀ := y₀) y t X = t := by
  simp [pev]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
