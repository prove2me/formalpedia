-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.carrierMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:46.161398+00:00
-- url     : https://prove2.me/submissions/d180b5b0-859c-4e17-9bc7-5a1ae1c90370

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_carrierMass_move_add_one

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace BranchReach
theorem _root_.solution
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    B.carrierMass D ≤ B.carrierMass C := by
  induction hreach with
  | refl => rfl
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      have hdrop :=
        B.carrierMass_move_add_one _ huv.ne hlegal huB hvB
      omega
end BranchReach
end TreeStack.OrientedBranch
