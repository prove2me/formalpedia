-- Prove2me | solution 1 for PI.SqfRootsInj.W.g_pow_sub_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:29.327221+00:00
-- url     : https://prove2.me/submissions/6198dae0-a4cf-4583-b361-323261d00d4d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover

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
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {g e : ℕ} (hg2 : 1 < g) (he : 1 ≤ e) : g ^ e - 1 ≠ 0 := by
  have := Nat.one_lt_pow (by omega : e ≠ 0) hg2
  omega
end PI.SqfRootsInj.W
