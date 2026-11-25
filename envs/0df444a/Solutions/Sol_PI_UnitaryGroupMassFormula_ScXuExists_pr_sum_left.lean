-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.pr_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:42:54.146611+00:00
-- url     : https://prove2.me/submissions/93de1142-1be8-4aa0-ad41-e1773e1fd84e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_pr_add_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (β : ι → Fin n → K) (x : Fin n → K) :
    pr P (∑ i ∈ s, β i) x = ∑ i ∈ s, pr P (β i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [pr]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_left, ih]
end PI.UnitaryGroupMassFormula.ScXuExists
