-- Prove2me | solution 1 for P2M_PI_FockWtDegWork_X_mul_monomial__8f48671e9716
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:22.639925+00:00
-- url     : https://prove2.me/submissions/6dacaff3-0705-4748-ae06-bb3675cdabcc

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

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
theorem _root_.solution {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by
  first
    | (rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul])
    | simp [MvPolynomial.X, MvPolynomial.monomial_mul]
end PI.FockWtDegWork
