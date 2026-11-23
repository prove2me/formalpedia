-- Prove2me | solution 1 for PI.FglPtW.Wk.serOver_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:25.156137+00:00
-- url     : https://prove2.me/submissions/b0c04fa6-e776-4061-a001-7e06ccc0e2c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPtW PI.FglPtW.Wk
open PI.AddIntG.Wk
variable {K : Type*} [CommRing K]
namespace PI.FglPtW.Wk
theorem _root_.solution (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by
  constructor
  · intro h
    refine ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, ?_⟩
    ext n
    first
    | rfl
    | simp [MvPowerSeries.coeff_map]
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2
end PI.FglPtW.Wk
