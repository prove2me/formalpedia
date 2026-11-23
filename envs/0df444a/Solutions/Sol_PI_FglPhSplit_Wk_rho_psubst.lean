-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.16899+00:00
-- url     : https://prove2.me/submissions/83a5550a-dbf1-4715-bf8d-64e41bd92704

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
theorem _root_.solution (P : PowerSeries K) {y : MvPowerSeries (ι ⊕ ι) K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (PowerSeries.subst y P) = PowerSeries.subst (rho (ι' := ι') y) P := by
  rw [rho_apply, rho_apply]
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hy)) hasSubst_inl]
end PI.FglPhSplit.Wk
