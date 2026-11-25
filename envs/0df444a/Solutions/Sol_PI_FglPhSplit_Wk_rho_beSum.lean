-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_beSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:02.774861+00:00
-- url     : https://prove2.me/submissions/64495768-a5e5-4022-b238-f586ecebb8ac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_X
import Theorems.Thm_PI_FglPhSplit_Wk_rho_be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
variable {ι ι' : Type} [Fintype ι]
variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0
namespace PI.FglPhSplit.Wk
theorem _root_.solution :
    rho (ι' := ι') (g.beSum ι) = ∑ e : ι, g.be (MvPowerSeries.X (Sum.inl (Sum.inl e)))
      (MvPowerSeries.X (Sum.inl (Sum.inr e))) := by
  unfold Dat.beSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [rho_be g hex0 hl0 (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _), rho_X, rho_X]
end PI.FglPhSplit.Wk
