-- Prove2me | solution 1 for PI.SwSandwichOfWork.Log_sgI_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:22.81538+00:00
-- url     : https://prove2.me/submissions/5cc96f59-a216-47be-b31b-3d048e87e38e

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : ((sgI k r i).val = r + k ↔ i.val = r + k) := by
  unfold sgI
  split_ifs <;> simp_all <;> omega
end PI.SwSandwichOfWork
