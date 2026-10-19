-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/25ed2350-40a6-41ba-9837-b947f7373b36

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ} {ι : Type*}
    (indices : Finset ι) (vectors : ι → Fin r → ℂ) :
    treeQuotientLinearForm (fun row => ∑ i ∈ indices, vectors i row) =
      ∑ i ∈ indices, treeQuotientLinearForm (vectors i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [treeQuotientLinearForm]
  | @insert i indices hi ih =>
      simp only [Finset.sum_insert hi]
      rw [treeQuotientLinearForm_add, ih]
end PermanentRollout
