-- Prove2me | solution 1 for PI.FockWtDegWork.fockAct2_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:42.54706+00:00
-- url     : https://prove2.me/submissions/352a2f5a-c277-43e6-99c3-f4a7c15236db

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
import Theorems.Thm_PI_FockWtDegWork_omE_diag_monomial
import Theorems.Thm_PI_FockWtDegWork_fockAct2_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution (p q r s : ℕ) (c : Ix r s) (β : Ln p q r s →₀ ℕ) :
    fockAct2 p q r s (Eab c c) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W2 c β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct2_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial]
  rw [← Finset.sum_smul, W2, Rat.cast_sum]
end PI.FockWtDegWork
