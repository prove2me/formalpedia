-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.monicDeg_fn_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:20.825426+00:00
-- url     : https://prove2.me/submissions/ae21953c-9461-40b2-ab33-1b2f99809153

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (d : ℕ) (c : Fin d → ZMod g) (i : Fin d) :
    (X ^ d + ∑ j, C (c j) * X ^ (j : ℕ) : (ZMod g)[X]).coeff i = c i := by
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.is_lt), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h).symm
  · simp
end PI.SqfPrimeFactor.W
