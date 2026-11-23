-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.669878+00:00
-- url     : https://prove2.me/submissions/9e4c3b42-9c3f-43c8-9311-2ddae15ac31d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (β x y : Fin n → K) : pr P β (x + y) = pr P β x + pr P β y := by
  unfold pr
  rw [Matrix.mulVec_add, dotProduct_add]
end PI.UnitaryGroupMassFormula.ScXuExists
