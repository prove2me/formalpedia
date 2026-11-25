-- Prove2me | solution 1 for PI.GalTorsConj.W.mulStable_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:09.45291+00:00
-- url     : https://prove2.me/submissions/acb12f96-47b5-4b21-b0ca-fdfce8a37905

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  rw [← nsmul_eq_mul]
  exact nsmul_mem hω n
end PI.GalTorsConj.W
