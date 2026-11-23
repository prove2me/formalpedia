-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_eq_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.747303+00:00
-- url     : https://prove2.me/submissions/1c0bf784-7ef9-4596-81a0-a4ac7928ce5d

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
theorem _root_.solution (β x : Fin n → K) : pr P β x = (β ᵥ* P) ⬝ᵥ x := by
  first
  | exact dotProduct_mulVec β P x
  | exact Matrix.dotProduct_mulVec β P x
  | simp [pr, dotProduct_mulVec]
end PI.UnitaryGroupMassFormula.ScXuExists
