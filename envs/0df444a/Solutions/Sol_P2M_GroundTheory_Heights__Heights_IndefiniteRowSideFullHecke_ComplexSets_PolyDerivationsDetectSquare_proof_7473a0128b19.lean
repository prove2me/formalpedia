-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_proof_7473a0128b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:13.332957+00:00
-- url     : https://prove2.me/submissions/ca6b2167-1ee2-4369-b422-848cf19d2e17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyKaehlerFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyDerivationsDetectSquare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27

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
noncomputable section
open IsLocalRing KaehlerDifferential TensorProduct
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PolyDerivationsDetectSquare
theorem _root_.solution (h₁ : PerfectFieldExtensionFormallySmooth.Statement)
    (h₂ : PolyKaehlerFree.Statement) : PolyDerivationsDetectSquare.Statement := by
  intro k _ n p _ g hg hD
  obtain ⟨q, hq⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k q with hqp | rfl
  · have : Fact q.Prime := ⟨hqp⟩
    let _ : Algebra (ZMod q) k := ZMod.algebra k q
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ (ZMod q) k n p g hg hD
  · have : CharZero k := CharP.charP_to_charZero k
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ ℚ k n p g hg hD
end PolyDerivationsDetectSquare
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
