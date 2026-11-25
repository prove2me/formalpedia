-- Prove2me | solution 1 for PI.QnHermHaar.nested_minor_expansion_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:38.094201+00:00
-- url     : https://prove2.me/submissions/5624cf2f-c0fb-4378-b636-43cf31c84d2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Theorems.Thm_PI_QnHermHaar_skip1Fun

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1)) := by
  simp only [tA, skip1Fun]
end PI.QnHermHaar
