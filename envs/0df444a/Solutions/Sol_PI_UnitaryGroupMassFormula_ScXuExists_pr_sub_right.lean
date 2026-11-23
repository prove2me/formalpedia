-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:28.083807+00:00
-- url     : https://prove2.me/submissions/5ae08275-37ce-4461-91e0-aa052e4ea245

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
theorem _root_.solution (β x y : Fin n → K) : pr P β (x - y) = pr P β x - pr P β y := by
  unfold pr
  rw [Matrix.mulVec_sub, dotProduct_sub]
end PI.UnitaryGroupMassFormula.ScXuExists
