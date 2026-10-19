-- Prove2me | solution 1 for PermanentRollout.sourceCircuit_ofList_ofFn_eq_span_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/d7df58e3-906d-4530-adef-d82e266687f0

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  change Ideal.span {p : R | p ∈ List.ofFn f} =
    Ideal.span (Set.range f)
  congr 1
  ext p
  simp
end PermanentRollout
