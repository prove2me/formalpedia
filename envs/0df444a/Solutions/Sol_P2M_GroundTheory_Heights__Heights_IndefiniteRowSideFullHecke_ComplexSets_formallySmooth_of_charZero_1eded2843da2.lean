-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_formallySmooth_of_charZero_1eded2843da2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:41.406422+00:00
-- url     : https://prove2.me/submissions/3ab0bd78-abab-4680-b33b-6a9eb3158f78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothExtensionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K : Type} [Field F] [Field K] [Algebra F K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution [CharZero F] : Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  have := hs.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact .of_algebraicIndependent_of_isSeparable hs.1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
