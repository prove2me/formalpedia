-- Prove2me | solution 1 for PI.QnHermHaar.star_transfer_diagonal_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:47.550659+00:00
-- url     : https://prove2.me/submissions/f4da6fd5-454d-43bb-8fa6-b55d97251fef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero

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
theorem _root_.solution (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) :
    star (tA E Y Yb x xb u 0 0) = tA E Y Yb x xb (star u) 0 0 := by
  show star (qminor E id id u) = qminor E id id (star u)
  rw [hSM A m m E ε hGl hE id id u, Int.units_mul_self]
  simp
end PI.QnHermHaar
