-- Prove2me | solution 1 for PI.SSE.integer_combination_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:24.288801+00:00
-- url     : https://prove2.me/submissions/3b3d5696-7d97-4048-a808-3decdffce12f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Reduce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (x y : ℂ) (m n : ℤ) : (m : ℂ) * x + (n : ℂ) * y ∈ PI.lat2 x y := by
  unfold PI.lat2
  rw [← zsmul_eq_mul, ← zsmul_eq_mul]
  exact AddSubgroup.add_mem _
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)
end PI.SSE
