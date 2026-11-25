-- Prove2me | solution 1 for P2M_PI_QnHermHaar_chatAlin__903b24350a7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:45.146905+00:00
-- url     : https://prove2.me/submissions/aa04a4ee-320a-4e8a-8235-b6023e62fa95

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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ l, β l • chatA E w a (Pi.single l 1) := by
  simp only [chatAβ]
  simp only [chatA, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring
end PI.QnHermHaar
