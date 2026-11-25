-- Prove2me | solution 1 for PI.SwSandwichOfWork.Log_Hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:34.131335+00:00
-- url     : https://prove2.me/submissions/7d03899d-129c-4ae9-afdc-0639f8609d83

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sgI k r i then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold Hpk sgI
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)
end PI.SwSandwichOfWork
