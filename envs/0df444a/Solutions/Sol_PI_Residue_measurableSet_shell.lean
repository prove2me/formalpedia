-- Prove2me | solution 1 for PI.Residue.measurableSet_shell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:56.698974+00:00
-- url     : https://prove2.me/submissions/37ea4067-6f8b-41e7-a0fc-def45049b143

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
theorem _root_.solution : MeasurableSet (shell K) := by
  have : shell K = fundamentalCone K ∩
      ({y | 1 / 2 < mixedEmbedding.norm y} ∩ {y | mixedEmbedding.norm y ≤ 1}) := by
    ext y
    simp only [shell, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  exact (measurableSet_fundamentalCone K).inter
    ((measurableSet_lt measurable_const (mixedEmbedding.continuous_norm K).measurable).inter
      (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const))
end PI.Residue
