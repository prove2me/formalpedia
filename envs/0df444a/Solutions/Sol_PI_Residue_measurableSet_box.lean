-- Prove2me | solution 1 for PI.Residue.measurableSet_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:47.611186+00:00
-- url     : https://prove2.me/submissions/afb05064-3c99-4166-955a-c7c1a5ca2d86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NormAtPlacePosOfNormPos

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
variable (K : Type) [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (r : InfinitePlace K → ℝ) : MeasurableSet (box K r) := by
  have : box K r = ⋂ w, {y | normAtPlace w y < r w} := by
    ext y; simp [box]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt (continuous_normAtPlace w).measurable measurable_const
end PI.Residue
