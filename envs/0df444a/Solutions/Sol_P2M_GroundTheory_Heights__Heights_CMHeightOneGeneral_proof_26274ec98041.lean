-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMHeightOneGeneral_proof_26274ec98041
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:03.184072+00:00
-- url     : https://prove2.me/submissions/3347ef74-bd8e-4eba-8908-3771afc2cb04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightOneGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightOneGeneral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_of_minimalPrimes_sup_span_6892ec4f36ad

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
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace CMHeightOneGeneral
theorem _root_.solution (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))
end CMHeightOneGeneral
end GroundTheory.Heights₂.Heights
