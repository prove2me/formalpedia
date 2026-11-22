-- Prove2me | solution 1 for PI.Residue.unitMul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:41.825797+00:00
-- url     : https://prove2.me/submissions/24e09b21-23f2-4285-8aae-0a813cc9e04a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero

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
open scoped ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable (K : Type) [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (u : (𝓞 K)ˣ) (y : mixedSpace K) : unitMul K u y = u • y := rfl
end PI.Residue
