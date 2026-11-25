-- Prove2me | solution 1 for PI.QnHermHaar.transfer_entry_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:27.910451+00:00
-- url     : https://prove2.me/submissions/ca9d30d2-731a-4c2a-ba91-cfbbdf0c51d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
import Theorems.Thm_PI_QnHermHaar_general_second_minor_expansion

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ l, ∑ p, Yb l * Y p * chat2A E (u - 1) (Pi.single p 1) x (Pi.single l 1) xb := by
  rw [general_second_minor_expansion E Yb Y (u - 1) x xb]
  try rfl
end PI.QnHermHaar
