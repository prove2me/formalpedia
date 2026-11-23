-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:29.212181+00:00
-- url     : https://prove2.me/submissions/0fdae4c8-71cc-4ae5-ad38-c5d89c10546b

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
theorem _root_.solution (F : MvPowerSeries (ι ⊕ ι) K) :
    (rho (ι' := ι') F) = MvPowerSeries.subst
      (fun j : ι ⊕ ι => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)) F := by
  exact MvPowerSeries.substAlgHom_apply _ _
end PI.FglPhSplit.Wk
