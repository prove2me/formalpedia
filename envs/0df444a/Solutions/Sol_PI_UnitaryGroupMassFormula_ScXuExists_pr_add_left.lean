-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:27.419544+00:00
-- url     : https://prove2.me/submissions/addcbf99-1c06-4e78-918d-0ef550d91748

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
theorem _root_.solution (β β' x : Fin n → K) : pr P (β + β') x = pr P β x + pr P β' x := by
  first
  | simp [pr]
  | simp [pr, dotProduct, Finset.sum_add_distrib, add_mul]
end PI.UnitaryGroupMassFormula.ScXuExists
