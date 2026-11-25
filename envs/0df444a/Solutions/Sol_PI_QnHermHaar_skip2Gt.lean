-- Prove2me | solution 1 for PI.QnHermHaar.skip2Gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:52.421455+00:00
-- url     : https://prove2.me/submissions/51637bf5-df75-4807-93ca-caf2a7c950a1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Theorems.Thm_PI_QnHermHaar_valSuccAbove
import Theorems.Thm_PI_QnHermHaar_valSkip2

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
theorem _root_.solution {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : ¬ (k : ℕ) < (i' : ℕ)) :
    (skip2 i' (i'.succAbove k) : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega
end PI.QnHermHaar
