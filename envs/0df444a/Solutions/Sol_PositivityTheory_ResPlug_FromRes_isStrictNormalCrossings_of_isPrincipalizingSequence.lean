-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_of_isPrincipalizingSequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:19:31.817149+00:00
-- url     : https://prove2.me/submissions/4485229c-3dee-4c13-9c4a-17b6b9233742

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_inSNCPosition_of_hasSNC
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_isStrictNormalCrossings_radical_prod
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_inSNCPosition_drop
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_support_exceptionalProduct_eq_drop
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_eq_radical


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
theorem _root_.solution {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    {I : X.IdealSheafData} {E : List X.IdealSheafData} {s : BlowupSequence X}
    (hE : HasSimpleNormalCrossings p E) (h : IsPrincipalizingSequence p I E s) :
    IsStrictNormalCrossings (reducedPreimage s.topMap I.support) := by
  obtain ⟨bd, hbd, hsupp⟩ := support_exceptionalProduct_eq_drop h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htop, hsm, -⟩ := h
  have : Smooth (s.topMap ≫ p) := hsm s.length le_rfl
  have key := isStrictNormalCrossings_radical_prod (s.topMap ≫ p) ((bd s.length).drop E.length)
    (inSNCPosition_drop (inSNCPosition_of_hasSNC (hbd s.length le_rfl)) E.length)
  have e : reducedPreimage s.topMap I.support = ((bd s.length).drop E.length).prod.radical := by
    refine reducedInverseImage_eq_radical _ _ _ ?_
    rw [← hsupp, ← htop, Scheme.IdealSheafData.support_comap]
    rfl
  rw [e]; exact key
end PositivityTheory.ResPlug.FromRes
