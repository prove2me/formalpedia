-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PerfectFieldExtensionFormallySmooth_proof_2401a84b68ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:00:03.892541+00:00
-- url     : https://prove2.me/submissions/2021b369-7ba4-4a6d-9b86-6e2fb638e94f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothExtensionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_formallySmooth_of_perfectField_of_charP_8405d43cece6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_formallySmooth_of_charZero_1eded2843da2

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PerfectFieldExtensionFormallySmooth
theorem _root_.solution : PerfectFieldExtensionFormallySmooth.Statement := by
  intro F K _ _ _ _
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := Fact.mk hp
    exact formallySmooth_of_perfectField_of_charP p
  · have := CharP.charP_to_charZero F
    exact formallySmooth_of_charZero
end PerfectFieldExtensionFormallySmooth
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
