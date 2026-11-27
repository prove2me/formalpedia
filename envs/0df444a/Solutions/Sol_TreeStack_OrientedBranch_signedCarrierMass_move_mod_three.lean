-- Prove2me | solution 1 for TreeStack.OrientedBranch.signedCarrierMass_move_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:53:23.640691+00:00
-- url     : https://prove2.me/submissions/5e8f68f0-f59b-4c9f-b3d9-ee8f38af75a1

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_OrientedBranch_signedCarrierMass_move

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) ≡ B.signedCarrierMass C [ZMOD 3] := by
  rw [B.signedCarrierMass_move C huv hu huB hvB, Int.modEq_iff_dvd]
  refine ⟨B.boundaryParityWeight u, ?_⟩
  ring
end TreeStack.OrientedBranch
