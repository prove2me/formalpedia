-- Prove2me | solution 1 for PI.Residue.normAtPlace_pos_of_norm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:41.587306+00:00
-- url     : https://prove2.me/submissions/95c54a83-1cac-44a9-97dd-caa40b640546

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
variable {K}
namespace PI.Residue
theorem _root_.solution {y : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (w : InfinitePlace K) : 0 < normAtPlace w y := by
  refine lt_of_le_of_ne (normAtPlace_nonneg w y) fun h => ?_
  exact hy.ne' (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h.symm⟩)
end PI.Residue
