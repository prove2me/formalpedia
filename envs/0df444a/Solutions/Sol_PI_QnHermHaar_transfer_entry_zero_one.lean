-- Prove2me | solution 1 for PI.QnHermHaar.transfer_entry_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:03.544624+00:00
-- url     : https://prove2.me/submissions/826a2785-0cd2-412f-8ea1-96f10daa594f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
import Theorems.Thm_P2M_PI_QnHermHaar_chatA__5d55b03eff4f

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
    tA E Y Yb x xb u 0 1 = -∑ l, Yb l * chatA E (u - 1) x (Pi.single l 1) := by
  show -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E (skip1 i) (skip1 j) (u - 1)) = _
  simp only [chatAβ, Finset.mul_sum, mul_smul_comm]
end PI.QnHermHaar
