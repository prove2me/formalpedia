-- Prove2me | solution 1 for PI.Residue.unitMul_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:34.084424+00:00
-- url     : https://prove2.me/submissions/b9ba39c9-0516-440a-b628-e9273b878d22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero
import Theorems.Thm_PI_Residue_unitMul_apply

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
theorem _root_.solution (u v : (𝓞 K)ˣ) : unitMul K u ∘ₗ unitMul K v = unitMul K (u * v) := by
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, unitMul_apply, mul_smul]
end PI.Residue
