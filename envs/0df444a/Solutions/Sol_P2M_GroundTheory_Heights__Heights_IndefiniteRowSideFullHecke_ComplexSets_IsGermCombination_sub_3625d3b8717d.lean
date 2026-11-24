-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_sub_3625d3b8717d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:29.922152+00:00
-- url     : https://prove2.me/submissions/821dda56-41f8-4bcc-99d3-07d3903724a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation

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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
theorem _root_.solution {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z - g z) :=
  (hf.add hg.neg).congr (Eventually.of_forall fun z => by ring)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
