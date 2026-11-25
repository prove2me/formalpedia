-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.pr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:09.950106+00:00
-- url     : https://prove2.me/submissions/9bd93319-1bf5-47eb-b5ff-ef4f7488a694

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Theorems.Thm_PI_PrimesDyadicRS_K_gcd_fact_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
open Real
namespace PI.PrimesDyadicRS.K
theorem _root_.solution {Q m : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ m) (hm : m < 131769) :
    pr Q m = if m.Prime then 1 else 0 := by
  by_cases h1 : m ≤ 362
  · have e := gcd_fact_iff (k := m - 1) h2 (by omega)
      (by rw [show m - 1 + 1 = m by omega]; nlinarith)
    simp only [pr, if_pos h1]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]
  · have e := gcd_fact_iff (k := 362) h2 (by omega) (by norm_num; omega)
    simp only [pr, if_neg h1, hQ]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]
end PI.PrimesDyadicRS.K
