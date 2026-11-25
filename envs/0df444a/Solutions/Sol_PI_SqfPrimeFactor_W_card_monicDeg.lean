-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.card_monicDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:29:40.550076+00:00
-- url     : https://prove2.me/submissions/25216646-5f9c-47c0-a51a-b2ef93ee4767

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Theorems.Thm_PI_SqfPrimeFactor_W_monicDeg_fn_coeff

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
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (d : ℕ) : (monicDeg g d).card = g ^ d := by
  unfold monicDeg
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, ZMod.card]
  · intro c c' h
    funext i
    have := congrArg (fun f : (ZMod g)[X] => f.coeff i) h
    simpa only [monicDeg_fn_coeff] using this
end PI.SqfPrimeFactor.W
