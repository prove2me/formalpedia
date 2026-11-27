-- Prove2me | solution 1 for TreeStack.OrientedBranch.exactBoundaryInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:05:32.664087+00:00
-- url     : https://prove2.me/submissions/4524cfc8-4e0a-40d6-bffc-de668b2eac3b

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_boundary_le_message
import Theorems.Thm_TreeStack_OrientedBranch_ClearOutcome_no_positive_boundary_of_message_nonpos
import Theorems.Thm_TreeStack_OrientedBranch_boundary_attainment

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T) :
    ExactBoundaryInvariant C B := by
  intro hOcc d hMsg q
  refine ⟨?_, ?_, ?_⟩
  · intro hPos
    exact boundary_attainment C B hOcc d hMsg q hPos
  · intro D hClear
    exact ClearOutcome.boundary_le_message
      B C q hOcc hMsg hClear
  · intro hNonpos
    exact ClearOutcome.no_positive_boundary_of_message_nonpos
      B C q hOcc hMsg hNonpos
end TreeStack.OrientedBranch
