-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.coe_support_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:09:56.836803+00:00
-- url     : https://prove2.me/submissions/49e6ad76-9152-405c-a7ad-7221d3dd6ccc

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
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) := by
  rw [Scheme.IdealSheafData.support_comap]; rfl
end PositivityTheory.ResPlug.FromRes
