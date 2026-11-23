-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.084623+00:00
-- url     : https://prove2.me/submissions/8bdeee48-b5ea-4484-b806-a6c90cc4504c

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
theorem _root_.solution (c : K) (β x : Fin n → K) : pr P (c • β) x = c * pr P β x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.mul_sum, mul_assoc]
end PI.UnitaryGroupMassFormula.ScXuExists
