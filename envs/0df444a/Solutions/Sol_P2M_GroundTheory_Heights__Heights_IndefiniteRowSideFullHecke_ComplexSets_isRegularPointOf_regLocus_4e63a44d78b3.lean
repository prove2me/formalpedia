-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_regLocus_4e63a44d78b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:17.024107+00:00
-- url     : https://prove2.me/submissions/4fc2b09b-04f3-4a51-88e9-22f2e541d740

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_regLocus_subset_369db4101cd9

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
theorem _root_.solution {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {x : σ → ℂ}
    (hx : x ∈ regLocus Y) : IsRegularPointOf (regLocus Y) x := by
  have hx' : IsRegularPointOf Y x := hx
  obtain ⟨hxY, d, A, O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hx'
  refine ⟨hx, d, A, O, V, g, hO, hV, hxV, hg, hAg, ?_⟩
  rw [← hYV]
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨regLocus_subset Y hz, hzV⟩
  · rintro ⟨hzY, hzV⟩
    exact ⟨⟨hzY, d, A, O, V, g, hO, hV, hzV, hg, hAg, hYV⟩, hzV⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
