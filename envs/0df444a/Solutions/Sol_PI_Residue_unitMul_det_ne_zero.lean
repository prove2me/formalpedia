-- Prove2me | solution 1 for PI.Residue.unitMul_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:19:18.274568+00:00
-- url     : https://prove2.me/submissions/988c4c93-d0e1-4743-80ac-b29315507adf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitMulDetNeZero
import Theorems.Thm_PI_Residue_unitMul_apply
import Theorems.Thm_PI_Residue_unitMul_comp

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
theorem _root_.solution (u : (𝓞 K)ˣ) : LinearMap.det (unitMul K u) ≠ 0 := by
  intro h
  have h1 : unitMul K u ∘ₗ unitMul K u⁻¹ = LinearMap.id := by
    rw [unitMul_comp, mul_inv_cancel]
    refine LinearMap.ext fun y => ?_
    rw [unitMul_apply, one_smul, LinearMap.id_apply]
  have := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, h, zero_mul, LinearMap.det_id] at this
  exact zero_ne_one this
end PI.Residue
