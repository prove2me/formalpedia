-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.locLatSat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:18.803999+00:00
-- url     : https://prove2.me/submissions/268158aa-f264-465f-902f-8a3aa788e85b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_sat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution : PI.LocLatSat.Stmt := by
  intro F E _ _ _ _ _ sig p A n Λ W hΛ
  exact sat A.ιE A.O Λ hΛ W
end PI.LocLatSat.UnitaryGroupMassFormula
