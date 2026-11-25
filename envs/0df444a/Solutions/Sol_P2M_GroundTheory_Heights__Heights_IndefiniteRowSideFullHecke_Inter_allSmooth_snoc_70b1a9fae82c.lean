-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_allSmooth_snoc_70b1a9fae82c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:51.061318+00:00
-- url     : https://prove2.me/submissions/9f54ebde-8528-4abb-9180-1cf9f17f14e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A : HermLine ι} (hA : IsSmoothHerm A) : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa using hA
  · simpa using hL i
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
