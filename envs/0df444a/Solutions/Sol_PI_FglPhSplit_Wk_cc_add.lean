-- Prove2me | solution 1 for PI.FglPhSplit.Wk.cc_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:26.42309+00:00
-- url     : https://prove2.me/submissions/40554e3c-256f-45f5-afe4-aa9c2e20bac7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst

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
theorem _root_.solution {σ : Type} {x y : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.constantCoeff (g.add x y) = 0 := by
  unfold Dat.add Dat.pt Dat.lg
  exact cc_psubst _ hex0 (by rw [map_add, cc_psubst _ hl0 hx, cc_psubst _ hl0 hy, add_zero])
end PI.FglPhSplit.Wk
