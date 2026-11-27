-- Prove2me | solution 1 for TreeStack.OrientedBranch.ClearOutcome.no_positive_boundary_of_message_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:48.260667+00:00
-- url     : https://prove2.me/submissions/0e0a2c67-ae72-4bd2-9bc3-f14208091f52

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_boundary_le_message

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace ClearOutcome
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hNonpos : (q : ℤ) + d ≤ 0) :
    ¬ ∃ D : Configuration V,
      B.ClearOutcome C q D ∧ 0 < D B.parent := by
  rintro ⟨D, hClear, hPos⟩
  have hle :=
    ClearOutcome.boundary_le_message B C q hOcc hMsg hClear
  have hPosInt : 0 < (D B.parent : ℤ) := by
    exact_mod_cast hPos
  omega
end ClearOutcome
end TreeStack.OrientedBranch
