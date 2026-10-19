-- Prove2me | solution 1 for PermanentRollout.finiteFree_maximalFiber_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/f141bd81-f67c-4349-a681-7b6fa1f50b0d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Free R S]
    (p : Ideal R) [p.IsMaximal] :
    Module.finrank (R ⧸ p)
      (S ⧸ p.map (algebraMap R S)) = Module.finrank R S := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  calc
    Module.finrank (R ⧸ p)
        (S ⧸ p.map (algebraMap R S)) =
      Module.finrank (R ⧸ p)
        (TensorProduct R (R ⧸ p) S) :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).toLinearEquiv.finrank_eq
    _ = Module.finrank R S := Module.finrank_baseChange
end PermanentRollout
