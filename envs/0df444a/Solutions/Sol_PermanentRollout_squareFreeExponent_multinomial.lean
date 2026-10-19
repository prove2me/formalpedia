-- Prove2me | solution 1 for PermanentRollout.squareFreeExponent_multinomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/fbbece4d-3ac1-4cbe-9362-ca27548c182e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareFreeExponent_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*}
    (rows : Finset ι) :
    (squareFreeExponent rows).multinomial = rows.card.factorial := by
  classical
  rw [Finsupp.multinomial]
  change
    ((squareFreeExponent rows).sum (fun _ n => n)).factorial /
        (squareFreeExponent rows).prod (fun _ n => n.factorial) =
      rows.card.factorial
  rw [squareFreeExponent_sum]
  have hfactor :
      (squareFreeExponent rows).prod (fun _ n => n.factorial) = 1 := by
    rw [Finsupp.prod, squareFreeExponent_support]
    apply Finset.prod_eq_one
    intro row hrow
    simp [squareFreeExponent_apply, hrow]
  rw [hfactor, Nat.div_one]
end PermanentRollout
