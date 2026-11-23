-- Prove2me | solution 1 for PI.FglPhSplit.Wk.pt_lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:20.545485+00:00
-- url     : https://prove2.me/submissions/6abfb96d-a546-4311-b7b0-cc82f8c93aa3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes

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
namespace PI.FglPhSplit.Wk
theorem _root_.solution (g : Dat K) {τ : Type} (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) {y : MvPowerSeries τ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : g.pt (g.lg y) = y := by
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  simp only [Dat.pt, Dat.lg]
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hy', hinv,
    PowerSeries.subst_X (R := K) hy']
end PI.FglPhSplit.Wk
