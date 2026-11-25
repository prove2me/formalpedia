-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:35.092396+00:00
-- url     : https://prove2.me/submissions/f4b52d15-463b-4f28-b573-617884a1a3eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst
import Theorems.Thm_PI_FglPhSplit_Wk_cc_add
import Theorems.Thm_PI_FglPhSplit_Wk_rho_add

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
    rho (ι' := ι') (g.be x y) = g.be (rho x) (rho y) := by
  unfold Dat.be Dat.phAt
  rw [map_sub, map_sub, rho_psubst _ (cc_add g hex0 hl0 hx hy), rho_psubst _ hx, rho_psubst _ hy,
    rho_add g hex0 hl0 hx hy]
end PI.FglPhSplit.Wk
