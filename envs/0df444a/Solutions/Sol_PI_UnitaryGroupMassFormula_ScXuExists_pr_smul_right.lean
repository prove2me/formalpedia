-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:45.834645+00:00
-- url     : https://prove2.me/submissions/a5e24acf-6772-46bd-a7ba-dd91c2704bee

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
theorem _root_.solution (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by
  unfold pr
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
end PI.UnitaryGroupMassFormula.ScXuExists
