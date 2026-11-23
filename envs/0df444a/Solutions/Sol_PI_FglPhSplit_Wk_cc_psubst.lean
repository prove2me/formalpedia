-- Prove2me | solution 1 for PI.FglPhSplit.Wk.cc_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:26.878865+00:00
-- url     : https://prove2.me/submissions/83e96aed-e883-47e4-9f22-8d3181c9e7bd

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
theorem _root_.solution {σ : Type} (P : PowerSeries K) (hP : PowerSeries.constantCoeff P = 0)
    {y : MvPowerSeries σ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst y P) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hy)]
  refine finsum_induction (p := fun x => x = 0) rfl (fun x z hx hz => by rw [hx, hz, add_zero]) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP, zero_smul]
  · rw [map_pow, hy, zero_pow hd.ne', smul_zero]
end PI.FglPhSplit.Wk
