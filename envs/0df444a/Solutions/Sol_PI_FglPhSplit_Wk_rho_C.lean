-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:25.32332+00:00
-- url     : https://prove2.me/submissions/638ba1e2-217c-4a18-a8f9-5a1944822461

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum

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
theorem _root_.solution (c : K) :
    rho (ι' := ι') (MvPowerSeries.C c : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.C c := by
  have e1 : ∀ (τ : Type), (MvPowerSeries.C c : MvPowerSeries τ K) = algebraMap K (MvPowerSeries τ K) c := by
    intro τ
    rw [MvPowerSeries.algebraMap_apply]
    rfl
  rw [e1, e1, AlgHom.commutes]
end PI.FglPhSplit.Wk
