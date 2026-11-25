-- Prove2me | solution 1 for P2M_PI_Residue_measurableSet_shell__efd4227c586e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:33.072702+00:00
-- url     : https://prove2.me/submissions/044b5520-1d0b-4cc7-911d-219b7f099154

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
theorem _root_.solution : MeasurableSet (shell K) := by
  have h1 : MeasurableSet {y : mixedSpace K | 1 / 2 < mixedEmbedding.norm y} :=
    (isOpen_lt continuous_const (mixedEmbedding.continuous_norm K)).measurableSet
  have h2 : MeasurableSet {y : mixedSpace K | mixedEmbedding.norm y ≤ 1} :=
    (isClosed_le (mixedEmbedding.continuous_norm K) continuous_const).measurableSet
  exact (measurableSet_fundamentalCone K).inter (h1.inter h2)
end PI.Residue
