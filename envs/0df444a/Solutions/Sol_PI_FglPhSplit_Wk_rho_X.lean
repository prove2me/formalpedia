-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.823832+00:00
-- url     : https://prove2.me/submissions/3f5c8936-71b4-4b99-aa52-41dc9e408246

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_apply

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
namespace PI.FglPhSplit.Wk
theorem _root_.solution (j : ι ⊕ ι) :
    rho (ι' := ι') (MvPowerSeries.X j : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.X (Sum.inl j) := by
  rw [rho_apply, MvPowerSeries.subst_X hasSubst_inl]
end PI.FglPhSplit.Wk
