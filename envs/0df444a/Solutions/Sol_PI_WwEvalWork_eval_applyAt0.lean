-- Prove2me | solution 1 for PI.WwEvalWork.eval_applyAt0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:16.834082+00:00
-- url     : https://prove2.me/submissions/f99def65-e0de-47f4-b23b-5d42fa2f3fee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
import Theorems.Thm_PI_WwEvalWork_Lsum_finset_sum
import Theorems.Thm_PI_WwEvalWork_Lsum_monomial
import Theorems.Thm_PI_WwEvalWork_peval_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}
namespace PI.WwEvalWork
theorem _root_.solution (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (x : Lt × ℕ × Fin N0 → ℂ_[l]) (P : MvPolynomial (PI.WwEval.KM.XZ Lt N0 N1) ℤ) :
    eval x (PI.WwEval.KM.applyAt0 N0 N1 l Th P) = Lsum (wt Th) (peval x P) := by
  conv_rhs => rw [as_sum P]
  rw [map_sum, Lsum_finset_sum, PI.WwEval.KM.applyAt0, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [peval_monomial, Lsum_monomial, eval_monomial, wt]
  ring
end PI.WwEvalWork
