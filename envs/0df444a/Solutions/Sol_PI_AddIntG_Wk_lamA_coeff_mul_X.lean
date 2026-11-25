-- Prove2me | solution 1 for PI.AddIntG.Wk.lamA_coeff_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:50.873158+00:00
-- url     : https://prove2.me/submissions/70425956-49f9-4179-8e4f-24af9cbc548c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero

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
theorem _root_.solution (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by
  rw [Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]
end PI.AddIntG.Wk
