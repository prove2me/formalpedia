-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.inSNCPosition_of_hasSNC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:43.482807+00:00
-- url     : https://prove2.me/submissions/f91ab0c6-7632-47eb-986e-d734b7e1ca7d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace PositivityTheory.ResPlug.FromRes
theorem _root_.solution {X : Scheme.{0}} {k : Type} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
    {E : List X.IdealSheafData} (h : HasSimpleNormalCrossings p E) : InStrictNormalCrossingPosition p E := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hx, m, c, hc, he, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, ⟨c, hc, he⟩, a, h1, h2, h3⟩
end PositivityTheory.ResPlug.FromRes
