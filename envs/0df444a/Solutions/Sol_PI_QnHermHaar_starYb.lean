-- Prove2me | solution 1 for PI.QnHermHaar.starYb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:47.077386+00:00
-- url     : https://prove2.me/submissions/3701ff1f-ffe7-481b-80bf-eca70fb8459e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Yb c) = ((ε c : ℤ) : ℂ) • Y c := by
  rw [hYb c, star_smul, star_star, star_intCast]
end PI.QnHermHaar
