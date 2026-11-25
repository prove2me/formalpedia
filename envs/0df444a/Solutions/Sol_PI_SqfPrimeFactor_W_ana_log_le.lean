-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.ana_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:52.392969+00:00
-- url     : https://prove2.me/submissions/86815126-7384-4f44-b2db-81aac2130b59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
import Theorems.Thm_PI_SqfPrimeFactor_W_ana_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (x : ℝ) (hx : 100 ≤ x) : Real.log x ≤ 0.0464 * x := by
  have he : Real.exp 1 ≤ 100 := by have := Real.exp_one_lt_d9; linarith
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hx)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h100 := ana_log
  simp only at h
  rw [div_le_div_iff₀ hx0 (by norm_num)] at h
  nlinarith
end PI.SqfPrimeFactor.W
