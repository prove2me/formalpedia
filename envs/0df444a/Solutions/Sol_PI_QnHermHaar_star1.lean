-- Prove2me | solution 1 for PI.QnHermHaar.star1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:24.757288+00:00
-- url     : https://prove2.me/submissions/94d5a363-8ee6-4915-8ce5-690406ae3ff1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Theorems.Thm_PI_QnHermHaar_intCastMul
import Theorems.Thm_PI_QnHermHaar_prodSA

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
theorem _root_.solution (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 1) → Fin (t + 1) → A) (ε : Fin (t + 1) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i j : Fin (t + 1)) (w : ℂ) :
    star (qminor E i.succAbove j.succAbove w) =
      (((ε i : ℤ) : ℂ) * ((ε j : ℤ) : ℂ)) • qminor E j.succAbove i.succAbove (star w) := by
  rw [hSM A (t + 1) t E ε hGl hE i.succAbove j.succAbove w, intCastMul, prodSA, prodSA,
    mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl
end PI.QnHermHaar
