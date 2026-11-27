-- Prove2me | solution 1 for P2M_GlobalTheory_T_isOpen_regularLocus_of_nagata__ee883f1d30e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:12.900473+00:00
-- url     : https://prove2.me/submissions/01445d31-2885-4e54-8ea2-3325455ceefa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagataStatement
import Theorems.Thm_GlobalTheory_isOpen_regularLocus_of_nagata


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  first | exact @GlobalTheory.isOpen_regularLocus_of_nagata | exact GlobalTheory.isOpen_regularLocus_of_nagata | (intros; apply GlobalTheory.isOpen_regularLocus_of_nagata <;> assumption)
end _root_.GlobalTheory.T
