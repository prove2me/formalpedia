-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.monicDeg_fn_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:40.236871+00:00
-- url     : https://prove2.me/submissions/61da2820-1bbc-4b53-8538-9b166cea170c

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
theorem _root_.solution (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)
end PI.SqfPrimeFactor.W
