-- Prove2me | solution 1 for PI.SwSandwichOfWork.normRL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:47.669975+00:00
-- url     : https://prove2.me/submissions/2eabee02-922c-47ac-9a2b-7a27f093a2cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution : NormRL := by
  intro k r X
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]
  simp [RL, realifyFun]
  ring
end PI.SwSandwichOfWork
