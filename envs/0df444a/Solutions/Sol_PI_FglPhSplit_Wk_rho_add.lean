-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:28.323298+00:00
-- url     : https://prove2.me/submissions/c4b7c781-97d9-40e6-b3f5-d28c81533a38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst
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
theorem _root_.solution {x y : MvPowerSeries (ι ⊕ ι) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (g.add x y) = g.add (rho x) (rho y) := by
  unfold Dat.add Dat.pt Dat.lg
  rw [rho_psubst _ (by rw [map_add, cc_psubst _ hl0 hx, cc_psubst _ hl0 hy, add_zero]), map_add,
    rho_psubst _ hx, rho_psubst _ hy]
end PI.FglPhSplit.Wk
