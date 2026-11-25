-- Prove2me | solution 1 for PI.QnHermHaar.mvC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:44.866769+00:00
-- url     : https://prove2.me/submissions/a1ff3ade-6d39-414b-ba42-256be003f1d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Theorems.Thm_PI_QnHermHaar_intCastMul

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
theorem _root_.solution (hMV : MoveVec) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
    (hGl : GlRel E) (hL : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (hC : ∀ a b, y a * y b = y b * y a) (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ) :
    ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (y (b j) * qminor E a (b ∘ j.succAbove) w) =
      ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  have h := hMV A n t E y hGl hL hC a b w
  simp only [intCastMul] at h
  push_cast at h
  exact h
end PI.QnHermHaar
