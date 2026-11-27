-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.signedCarrierMass_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:54:20.128989+00:00
-- url     : https://prove2.me/submissions/762be845-722d-472e-ad5b-a3ab7af2b1d5

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_move_mod_three

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
    B.signedCarrierMass D ≡ B.signedCarrierMass C [ZMOD 3] := by
  induction hreach with
  | refl => exact Int.ModEq.refl _
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      exact (B.signedCarrierMass_move_mod_three _ huv hlegal huB hvB).trans ih
end BranchReach
end TreeStack.OrientedBranch
