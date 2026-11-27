-- Prove2me | solution 1 for TreeStack.rootSignatureFluxSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:42.299175+00:00
-- url     : https://prove2.me/submissions/2d8f3108-27f6-4774-af1b-76f1a46bff88

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (m : MoveSignature T) (r : V) :
    rootSignatureFluxSum m r =
      (m.incoming r : ℤ) - 2 * (m.outgoing r : ℤ) := by
  rw [rootSignatureFluxSum, MoveSignature.incoming, MoveSignature.outgoing]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
end TreeStack
