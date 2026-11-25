-- Prove2me | solution 1 for P2M_PI_Residue_measurableSet_hit__413fd930b60e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:28.386073+00:00
-- url     : https://prove2.me/submissions/36678912-0054-4f9f-aa41-349be4342868

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (ρ : ℝ) (x : mixedSpace K) : MeasurableSet (hit K ρ x) := by
  have : hit K ρ x = ⋂ w, {y | normAtPlace w y * normAtPlace w x < ρ} := by
    ext y; simp [hit]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (isOpen_lt ((continuous_normAtPlace w).mul continuous_const) continuous_const).measurableSet
end PI.Residue
