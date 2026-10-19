-- Prove2me | solution 1 for PermanentRollout.incidence_mvPolynomial_totalDegree_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/241128ba-30de-4a34-b211-6e7392efb44c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : MvPolynomial σ R) :
    (MvPolynomial.map f g).totalDegree ≤ g.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset f g)
end PermanentRollout
