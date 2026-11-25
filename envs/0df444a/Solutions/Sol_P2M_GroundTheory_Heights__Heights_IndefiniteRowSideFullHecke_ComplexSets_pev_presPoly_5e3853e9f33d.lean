-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_presPoly_5e3853e9f33d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:10.752849+00:00
-- url     : https://prove2.me/submissions/e5d171ae-2dfa-47aa-b3ea-9df8f38a3aa6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_evalAt_apply_3dcf9480b1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_C_84d2b4612e3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_X_1c14eb6f22af
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.evalAt_apply
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_C
attribute [local simp] GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.pev_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) (y : Fin d → ℂ) (t : ℂ) :
    pev y t (presPoly c hc) = t ^ N + ∑ j, c j y * t ^ (j : ℕ) := by
  simp [presPoly, map_sum]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
