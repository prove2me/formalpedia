-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isProjPrime_bot_space_7322bb62afb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:08.500793+00:00
-- url     : https://prove2.me/submissions/0a13179a-bf33-493b-9486-eff295674663

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n : ℕ) : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) where
  isPrime := Ideal.isPrime_bot
  isHomog f hf d := by
    rw [Ideal.mem_bot] at hf ⊢
    rw [hf, map_zero]
  isRelevant := ⟨0, fun hX => X_ne_zero (0 : Fin (n + 1)) (Ideal.mem_bot.mp hX)⟩
end GroundTheory.Heights₂.Heights
