-- Prove2me | solution 1 for TreeStack.OrientedBranch.MoveSignature.root_balance_with_child_flux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:53:28.688418+00:00
-- url     : https://prove2.me/submissions/765e86a1-ffc0-4d50-ad9a-b0d7e2eca68c

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_incoming_root_eq_parent_add_children
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_outgoing_root_eq_parent_add_children
import Theorems.Thm_TreeStack_OrientedBranch_signatureChildFluxSum_eq

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace MoveSignature
theorem _root_.solution
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hbal : m.BalancesAt C B.root) :
    (C B.root : ℤ) + signatureChildFluxSum m B +
        (m.count B.parent B.root : ℤ) -
      2 * (m.count B.root B.parent : ℤ) = 0 := by
  rw [MoveSignature.BalancesAt,
    MoveSignature.incoming_root_eq_parent_add_children m B,
    MoveSignature.outgoing_root_eq_parent_add_children m B] at hbal
  rw [signatureChildFluxSum_eq]
  ring_nf at hbal ⊢
  exact hbal
end MoveSignature
end TreeStack.OrientedBranch
