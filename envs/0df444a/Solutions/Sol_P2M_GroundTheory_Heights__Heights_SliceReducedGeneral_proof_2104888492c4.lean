-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceReducedGeneral_proof_2104888492c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:09:40.075254+00:00
-- url     : https://prove2.me/submissions/7571add4-b9c1-4a0d-8d14-0c69ed09802d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceUnmixedGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAt_of_associatedPrimes_7c015fdc89c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace SliceReducedGeneral
theorem _root_.solution (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩
end SliceReducedGeneral
end GroundTheory.Heights₂.Heights
