-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.card_bad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:59:57.60332+00:00
-- url     : https://prove2.me/submissions/0e1bc6d2-5290-41ef-b2fd-d52e83a96b08

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_mul_injOn
import Theorems.Thm_PI_SqfPrimeFactor_W_card_monicDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (r p : ℕ) (hp : r < 2 * p) :
    (bad g r p).card = (irrDeg g p).card * g ^ (r - p) := by
  unfold bad
  rw [Finset.card_image_of_injOn (mul_injOn r p hp), Finset.card_product, card_monicDeg]
end PI.SqfPrimeFactor.W
