-- Prove2me | solution 1 for PI.AddIntG.Wk.coeff_termS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:25.376648+00:00
-- url     : https://prove2.me/submissions/b97815d8-f4d1-4936-bb7c-444b8e1336b9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp
end PI.AddIntG.Wk
