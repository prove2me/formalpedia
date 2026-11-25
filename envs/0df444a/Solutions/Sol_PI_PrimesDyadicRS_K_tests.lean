-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.tests
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:10.514493+00:00
-- url     : https://prove2.me/submissions/16029729-d79e-449a-b50e-578404e0c1eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
import Theorems.Thm_PI_PrimesDyadicRS_K_D_two
import Theorems.Thm_PI_PrimesDyadicRS_K_loop_sound
import Theorems.Thm_PI_PrimesDyadicRS_K_force_eq
import Theorems.Thm_PI_PrimesDyadicRS_K_run1
import Theorems.Thm_PI_PrimesDyadicRS_K_run2
import Theorems.Thm_PI_PrimesDyadicRS_K_run3
import Theorems.Thm_PI_PrimesDyadicRS_K_run4


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
theorem _root_.solution : ∀ m, 41 ≤ m → m < 131072 → tstR m (D m) = true := by
  have r1 := run1
  have r2 := run2
  have r3 := run3
  have r4 := run4
  rw [run, force_eq] at r1 r2 r3 r4
  obtain ⟨⟨_, e1⟩, t1⟩ := loop_sound rfl _ _ _ r1 (by norm_num) (by norm_num) D_two.symm
  obtain ⟨⟨_, e2⟩, t2⟩ := loop_sound rfl _ _ _ r2 (by norm_num) (by norm_num) e1
  obtain ⟨⟨_, e3⟩, t3⟩ := loop_sound rfl _ _ _ r3 (by norm_num) (by norm_num) e2
  obtain ⟨_, t4⟩ := loop_sound rfl _ _ _ r4 (by norm_num) (by norm_num) e3
  intro m h1 h2
  by_cases a1 : m < 32768
  · exact t1 m (by omega) (by omega) h1
  by_cases a2 : m < 65536
  · exact t2 m (by omega) (by omega) h1
  by_cases a3 : m < 98304
  · exact t3 m (by omega) (by omega) h1
  · exact t4 m (by omega) (by omega) h1
end PI.PrimesDyadicRS.K
